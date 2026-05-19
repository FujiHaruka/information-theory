# T3-A Constrained Maximum Entropy ムーンショット計画 🌙

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-A. Constrained Maximum Entropy (Lagrange / exponential family)」
>
> **Inventory (Phase 0 完了)**: [`max-entropy-constrained-mathlib-inventory.md`](./max-entropy-constrained-mathlib-inventory.md)
>
> **Predecessor / 再利用基盤** (全て publish 済、本 plan からは黒箱 reuse):
> - `Common2026/Shannon/MaxEntropy.lean` (269 行) — `entropy_le_log_card`, `entropy_eq_log_card_iff`,
>   `klDiv_uniformOn_univ_toReal_eq` (uniform 退化形 identity、本 plan のテンプレ source)
> - `Common2026/Shannon/CsiszarProjection.lean` (488 行) — `klDivPmf`, `klDivPmf_nonneg`,
>   `klDivPmf_strictConvexOn_left`, `csiszar_projection_exists`, `csiszar_projection_unique`,
>   `csiszar_pythagoras_inequality`, `continuous_klDivPmf_left`
> - `Common2026/Shannon/Chernoff.lean` Tier 0 — `klDivPmf_self_eq_zero` (`P → 0 < P a → klDivPmf P P = 0`)
> - `Common2026/Shannon/DifferentialEntropy.lean:510-787` — `differentialEntropy_le_gaussian_of_variance_le`
>   + `differentialEntropy_eq_gaussian_iff`、**variance 制約特例 = T3-A pmf 形の連続版テンプレ写経 source**
> - `Common2026/Shannon/Bridge.lean:43` — `entropy μ X := ∑ x, Real.negMulLog ((μ.map X).real {x})`
>
> **Goal (短形)**: 新規ファイル `Common2026/Shannon/MaxEntropyConstrained.lean` で
> Cover-Thomas Theorem 12.1.1 (Constrained Maximum Entropy) の **pmf 形主定理** を、
> exponential family ansatz `λ : Fin k → ℝ` を **外から受け取る pass-through 形** で publish する。
> **0 sorry / 0 warning**、Tier 1 baseline ~200 行、Tier 2 (uniqueness 込み) ~280 行。
>
> **撤退ライン**: [L-S1] Tier 1 (上界のみ) 単独 publish / [L-S2] Csiszar (B) 経路 fallback /
> [L-S3] 単一制約 `k = 1` 縮退 / [L-P1] ψ 凸性が uniqueness scope 外に漏れる場合 (詳細 §撤退ライン)。

## Status (2026-05-19)

**Phase 0 (Mathlib + Common2026 在庫) 完了** — inventory で「**既存率 ~80%、KKT 不要、規模 ~250-350 行
(親計画 400-700 は過大評価)**」を確定。Tier 1 (主定理上界) → Tier 2 (uniqueness) → (任意) Tier 3
(特例展開) の段階的 publish 設計で着手準備完了。

**2026-05-19 更新**: **Tier 2 (Phase A + B + C + D) 完成、0 sorry / 0 warning publish**。
`Common2026/Shannon/MaxEntropyConstrained.lean` (~361 行) で
`gibbsPmf` + `gibbsPmf_mem_stdSimplex` + `entropy_le_gibbs_of_constraints` +
`entropy_eq_gibbs_iff_of_constraints` の 4 件を主定理として publish。
規模見積もり ~280 行に対して +30% (制約: Phase B-1 核 identity の手書き展開 ~90 行が
重力中心、Phase C は 2 補題 ~80 行で完了)。

## 進捗

- [x] Phase 0 — Mathlib + Common2026 在庫 ✅ → [`max-entropy-constrained-mathlib-inventory.md`](./max-entropy-constrained-mathlib-inventory.md)
- [x] Phase A — `gibbsPmf` 定義 + 基本性質 (Tier 0, ~80 行) ✅
- [x] Phase B — Gibbs 不等式主定理 (Tier 1 baseline, +~140 行) ✅
- [x] Phase C — Uniqueness (Tier 2 理想, +~80 行) ✅
- [x] Phase D — 主定理 wrapper + library 編入 (~20 行) ✅
- [ ] (任意) Phase E — 特例展開 (uniform / exponential / 2-point) Tier 3 stretch 📋

## ゴール / Approach

### 最終到達点 (Tier 2 完成形)

新規ファイル `Common2026/Shannon/MaxEntropyConstrained.lean` で 4 件 publish:

```lean
namespace InformationTheory.Shannon.MaxEntropyConstrained

/-- Boltzmann-Gibbs exponential family pmf, parametrized by Lagrange `lam : Fin k → ℝ`. -/
noncomputable def gibbsPmf {α : Type*} [Fintype α]
    {k : ℕ} (f : Fin k → α → ℝ) (lam : Fin k → ℝ) : α → ℝ :=
  fun x => Real.exp (∑ i, lam i * f i x) / ∑ y, Real.exp (∑ i, lam i * f i y)

/-- `gibbsPmf f lam ∈ stdSimplex ℝ α`. -/
theorem gibbsPmf_mem_stdSimplex
    {α : Type*} [Fintype α] [Nonempty α]
    {k : ℕ} (f : Fin k → α → ℝ) (lam : Fin k → ℝ) :
    gibbsPmf f lam ∈ stdSimplex ℝ α

/-- **T3-A 主定理 (Tier 1)** — 制約 `𝔼_P[f_i] = c_i` 下で `H(P) ≤ H(gibbsPmf f λ)`。
    `lam` は **ansatz として外から受け取る**: gibbs 側も同じ制約を満たす hypothesis を要求。 -/
theorem entropy_le_gibbs_of_constraints
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {k : ℕ} (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
    (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
    (lam : Fin k → ℝ)
    (h_gibbs_constraints : ∀ i, ∑ x, gibbsPmf f lam x * f i x = c i) :
    ∑ x, Real.negMulLog (P x) ≤ ∑ x, Real.negMulLog (gibbsPmf f lam x)

/-- **T3-A uniqueness (Tier 2)** — 等号成立 ⟺ `P = gibbsPmf f λ`。 -/
theorem entropy_eq_gibbs_iff_of_constraints
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {k : ℕ} (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
    (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
    (lam : Fin k → ℝ)
    (h_gibbs_constraints : ∀ i, ∑ x, gibbsPmf f lam x * f i x = c i) :
    ∑ x, Real.negMulLog (P x) = ∑ x, Real.negMulLog (gibbsPmf f lam x)
      ↔ P = gibbsPmf f lam

end InformationTheory.Shannon.MaxEntropyConstrained
```

### Approach (overall strategy / shape of solution)

**戦略の shape** — KKT / Lagrange duality は Mathlib に**実装されていない**
(`LagrangeMultipliers.lean:22-24` で TODO 明記、KKT 不在)。本 plan ではこれを **回避する Gibbs +
`klDivPmf ≥ 0` 直接ルート** を採用する:

```
0 ≤ klDivPmf P (gibbsPmf f λ)       -- Gibbs 不等式 (CsiszarProjection.klDivPmf_nonneg)
  = ∑ x, P x · (log P x - log gibbsPmf f λ x)
  = ∑ x, P x · log P x - ∑ x, P x · (∑ i, λ i · f i x - log Z(λ))
  = -H(P) - ⟨λ, 𝔼_P[f]⟩ + log Z(λ)        -- P ∈ stdSimplex で ∑ P x = 1
  = -H(P) - ⟨λ, c⟩ + log Z(λ)              -- hP_constraints で 𝔼_P[f] = c

∴ H(P) ≤ log Z(λ) - ⟨λ, c⟩

同様に gibbs 側で:
  0 = klDivPmf (gibbsPmf f λ) (gibbsPmf f λ)       -- Chernoff.klDivPmf_self_eq_zero
    = -H(gibbsPmf f λ) - ⟨λ, c⟩ + log Z(λ)         -- h_gibbs_constraints で同じ c

∴ H(gibbsPmf f λ) = log Z(λ) - ⟨λ, c⟩

ゆえに H(P) ≤ H(gibbsPmf f λ)
```

**鍵となる algebraic identity** (Tier 1 の核):

```
klDivPmf Q (gibbsPmf f λ) = -H(Q) - ⟨λ, 𝔼_Q[f]⟩ + log Z(λ)
                            (Q ∈ stdSimplex 上で成立)
```

これを `lemma klDivPmf_gibbsPmf_eq` として 1 本切り出すと、Tier 1 主定理 + Tier 2 uniqueness の
両方が「Q := P」「Q := gibbsPmf f λ」の 2 回呼び出しで完結する。**全体の重力中心はここ 1 本**。

**Mathlib-shape-driven の設計選択** — inventory §C で確定したように、本 plan の主役は
`CsiszarProjection.klDivPmf : (α → ℝ) → (α → ℝ) → ℝ` (= pmf 形 KL) であり、Mathlib の
`Measure.tilted` は使わない (使うと `Measure.real {x}` ⇄ pmf 経路の bridge が増える)。
理由:

1. **Csiszar 既存 API が pmf 形に閉じている** (`klDivPmf_nonneg`, `_strictConvexOn_left`,
   `csiszar_projection_*`, `klDivPmf_self_eq_zero`)。
2. **`Real.exp / Real.log / rpow` の算術だけで gibbs と log Z が閉じる** — Mathlib `Tilted` の
   `rnDeriv` / `=ᵐ` 議論を完全に回避できる。
3. **Tier 2 uniqueness** は `klDivPmf P Q = 0 ↔ P = Q` (CsiszarProjection の strict convexity から
   `csiszar_projection_unique` 経路で local lemma 1 本) で取れる。`klDiv_eq_zero_iff` (Measure 形)
   の `[IsFiniteMeasure]` 前提を踏まなくて済む。

**ansatz pass-through 設計** — 主定理の signature で `lam : Fin k → ℝ` と
`h_gibbs_constraints` を**外から取る**ことで、ψ(λ) の凸性 / Lagrange 双対性 / inverse 関数定理
等の Mathlib 不在の道具立てを**完全に回避**する。教科書 12.1.1 の "Lagrange multiplier `λ` の
存在" は本 plan の scope-out (Tier 3 stretch、別 seed `max-entropy-constrained-existence-*` 候補)。

**4 段の論理展開** (Phase A → D):

1. **Phase A**: `gibbsPmf` 定義 (textbook `exp(⟨λ,f⟩) / Z` 直接形) + `∈ stdSimplex` +
   各 `x` で `0 < gibbsPmf f λ x` (positivity、`Real.exp_pos` + 分母 positive)。
2. **Phase B**: 核 identity `klDivPmf_gibbsPmf_eq` を **算術操作だけ**で取り、それを
   Gibbs `klDivPmf_nonneg` + `klDivPmf_self_eq_zero` の 2 回呼び出しで Tier 1 主定理に合成。
3. **Phase C**: Tier 1 等式バージョンに `csiszar_projection_unique` + strict convexity を
   被せて P = gibbs 一意性。または直接 strict Jensen
   (`Real.strictConcaveOn_negMulLog` + `StrictConcaveOn.lt_map_sum`) 経路で替えが効く。
4. **Phase D**: 主定理 statement の文言整地 + docstring + `Common2026.lean` 編入 + 仕上げ。

### Approach 図

```
Phase 0  : Mathlib + Common2026 在庫                            ← 完了済
           ────────────────────────────────────────────────
Phase A  : gibbsPmf 定義 + 基本性質 (positivity, stdSimplex)    ← 0.3 セッション (Tier 0 baseline)
Phase B  : klDivPmf_gibbsPmf_eq identity + Tier 1 主定理        ← 0.5-0.7 セッション
           ←──── 撤退ライン L-S1 (Tier 1 単独 publish) ────────→
           ────────────────────────────────────────────────
Phase C  : Tier 2 uniqueness                                    ← 0.3-0.5 セッション
Phase D  : 主定理 wrapper + library 編入                        ← 0.1-0.2 セッション
           ────────────────────────────────────────────────
(任意) Phase E : 特例展開 (uniform / 2-point exponential)       ← Tier 3 stretch
```

### 規模見積 (Tier 別)

| Tier | scope | 自作 | 累積行数 | publish 形 |
|---|---|---|---|---|
| **Tier 0** | gibbsPmf def + positivity + stdSimplex | Phase A | ~80 行 | def + 基本性質 (主定理 sorry) |
| **Tier 1** | + 核 identity + Gibbs 不等式上界主定理 | Phase B | ~200 行 | `entropy_le_gibbs_of_constraints` (Tier 1 baseline 完成) |
| **Tier 2** | + uniqueness | Phase C | ~280 行 | `entropy_eq_gibbs_iff_of_constraints` (理想完成形) |
| **Tier 3** | + 特例 (uniform / 2-point / exponential discretized) | Phase E | ~350-400 行 | stretch (撤退時 scope-out) |

時間 budget: **1 セッション目標 Tier 1**。Tier 2 が同セッションで届かなければ judgement log
追記して別 plan に分離 (撤退ライン L-S1)。

### ファイル構成 (Phase D 完了想定)

```
Common2026/Shannon/
  MaxEntropyConstrained.lean ← 新規 (~280 行 Tier 2 / ~200 行 Tier 1 baseline)
  MaxEntropy.lean            ← 既存、変更なし (uniform 退化形、Phase B identity 整理時に
                               `klDiv_uniformOn_univ_toReal_eq` の証明テクニックを写経)
  CsiszarProjection.lean     ← 既存、変更なし (klDivPmf, klDivPmf_nonneg,
                               klDivPmf_strictConvexOn_left, csiszar_projection_unique)
  Chernoff.lean              ← 既存、変更なし (klDivPmf_self_eq_zero)
  DifferentialEntropy.lean   ← 既存、変更なし (Phase D 写経 source、
                               `differentialEntropy_le_gaussian_of_variance_le` 証明構造)
  Bridge.lean                ← 既存、変更なし (entropy)
Common2026.lean              ← `import Common2026.Shannon.MaxEntropyConstrained` 追記
```

## 依存関係

完了済 (黒箱 reuse、本 plan で再証明しない):

- [x] `Common2026/Shannon/MaxEntropy.lean` — `entropy_le_log_card`, `entropy_eq_log_card_iff`,
  `klDiv_uniformOn_univ_toReal_eq` (uniform 制約退化形、本 plan は **f := 0 で T3-A から再導出可**
  だが、既存版を黒箱として残す。再導出は Phase E stretch)
- [x] `Common2026/Shannon/CsiszarProjection.lean` — `klDivPmf`, `klDivPmf_nonneg`,
  `klDivPmf_strictConvexOn_left` (Tier 2 uniqueness の strict 凸性源), `csiszar_projection_exists`,
  `csiszar_projection_unique` (Tier 2 で reference Q = gibbs を取り直して呼ぶ)
- [x] `Common2026/Shannon/Chernoff.lean` Tier 0 — `klDivPmf_self_eq_zero`
  (Tier 1 で `gibbsPmf` 自身の KL = 0 を即取り)
- [x] `Common2026/Shannon/DifferentialEntropy.lean:510-787` — `differentialEntropy_le_gaussian_of_variance_le`,
  `differentialEntropy_eq_gaussian_iff` (**Phase B / C のテンプレ写経 source**:
  `volume → uniformOn univ` で pmf 形に縮める同じ証明構造)
- [x] Mathlib `Real.exp`, `Real.log`, `Real.negMulLog` (`Mathlib/Analysis/SpecialFunctions/`)
- [x] Mathlib `Real.strictConcaveOn_negMulLog`, `Real.concaveOn_negMulLog`
  (`Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:224, 227`、Tier 2 uniqueness 代替路)
- [x] Mathlib `stdSimplex`, `convex_stdSimplex`, `stdSimplex_subset_Icc`
  (`Mathlib/Analysis/Convex/StdSimplex.lean`)
- [x] Mathlib `Finset.sum_*` 系 (分配・線形性、特に `Finset.sum_mul`, `Finset.mul_sum`,
  `Finset.sum_add_distrib`, `Finset.sum_comm`)

---

## Phase 0 — Mathlib + Common2026 API 在庫 ✅

完了 (`docs/shannon/max-entropy-constrained-mathlib-inventory.md`, 454 行)。

主結論:

- **既存率 ~80%** (主要 API 35+ 項目): Csiszar pmf 経路 + Gibbs `klDivPmf_nonneg` + DifferentialEntropy
  テンプレで完備
- **KKT 不要、Lagrange API 不使用** — pmf 経路 + ansatz pass-through で完全回避
- **規模見積**: ~250-350 行 (親計画 400-700 は過大)
- **撤退ライン**: 親計画の "Lagrange + KKT" 撤退は**発動なし**、新規撤退ライン 4 件 (L-S1〜L-P1)
  を本 plan で正式 import

---

## Phase A — `gibbsPmf` 定義 + 基本性質 📋

### スコープ

`gibbsPmf` を pmf 形 (`α → ℝ`) で定義 (Mathlib `Measure.tilted` を**使わない**、判断ログ #1)。
positivity (`0 < gibbsPmf f λ x`) と `gibbsPmf f λ ∈ stdSimplex ℝ α` を取り、Phase B での
algebraic 操作の足場を完成させる。

### Done 条件 (Tier 0 baseline)

- `gibbsPmf` 定義 publish
- `gibbsPmf_pos` (各 `x` で `0 < gibbsPmf f λ x`)、`gibbsPmf_sum_eq_one`、`gibbsPmf_mem_stdSimplex`
- `lake env lean Common2026/Shannon/MaxEntropyConstrained.lean` で skeleton clean
  (Phase B / C / D は `sorry` 残し)
- 主定理 `entropy_le_gibbs_of_constraints` / `entropy_eq_gibbs_iff_of_constraints` は
  skeleton `:= by sorry` のまま

### ステップ

- [ ] **A-0 skeleton**: `MaxEntropyConstrained.lean` 新規ファイルに全主定理 + 補助補題を
  `:= by sorry` で並べた skeleton を Write。`import Common2026.Shannon.{MaxEntropy,
  CsiszarProjection, Chernoff}` + namespace + `open` を整備。LSP 診断で type-check OK 確認
  (CLAUDE.md "Skeleton-driven Development")。

- [ ] **A-1 `gibbsPmf` 定義**:
  ```lean
  noncomputable def gibbsPmf {α : Type*} [Fintype α]
      {k : ℕ} (f : Fin k → α → ℝ) (lam : Fin k → ℝ) : α → ℝ :=
    fun x => Real.exp (∑ i, lam i * f i x) / ∑ y, Real.exp (∑ i, lam i * f i y)
  ```
  分母を **`gibbsZ f lam : ℝ`** として独立 def 化するかは A-1 で確定 (Phase B で `log Z(λ)`
  が頻出するため、独立 def 化推奨)。

- [ ] **A-2 `gibbsZ_pos`** (分母 positivity):
  ```lean
  lemma gibbsZ_pos {α : Type*} [Fintype α] [Nonempty α]
      {k : ℕ} (f : Fin k → α → ℝ) (lam : Fin k → ℝ) :
      0 < ∑ y, Real.exp (∑ i, lam i * f i y)
  ```
  `Finset.sum_pos` + `Real.exp_pos` + `Finset.univ_nonempty` (from `[Nonempty α]`)。

- [ ] **A-3 `gibbsPmf_pos`**:
  ```lean
  lemma gibbsPmf_pos {α : Type*} [Fintype α] [Nonempty α]
      {k : ℕ} (f : Fin k → α → ℝ) (lam : Fin k → ℝ) (x : α) :
      0 < gibbsPmf f lam x
  ```
  `Real.exp_pos` / `gibbsZ_pos` + `div_pos`。

- [ ] **A-4 `gibbsPmf_sum_eq_one`**:
  ```lean
  lemma gibbsPmf_sum_eq_one {α : Type*} [Fintype α] [Nonempty α]
      {k : ℕ} (f : Fin k → α → ℝ) (lam : Fin k → ℝ) :
      ∑ x, gibbsPmf f lam x = 1
  ```
  `Finset.sum_div` で分母を外に出し、`div_self (ne_of_gt gibbsZ_pos)`。

- [ ] **A-5 `gibbsPmf_mem_stdSimplex`**:
  ```lean
  lemma gibbsPmf_mem_stdSimplex {α : Type*} [Fintype α] [Nonempty α]
      {k : ℕ} (f : Fin k → α → ℝ) (lam : Fin k → ℝ) :
      gibbsPmf f lam ∈ stdSimplex ℝ α
  ```
  `stdSimplex` 定義 (`{f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}`) に A-3 (positivity → nonneg) +
  A-4 を直接代入。

- [ ] **A-6 `log_gibbsPmf` 閉形** (Phase B 入口):
  ```lean
  lemma log_gibbsPmf {α : Type*} [Fintype α] [Nonempty α]
      {k : ℕ} (f : Fin k → α → ℝ) (lam : Fin k → ℝ) (x : α) :
      Real.log (gibbsPmf f lam x)
        = (∑ i, lam i * f i x) - Real.log (∑ y, Real.exp (∑ i, lam i * f i y))
  ```
  `Real.log_div (Real.exp_ne_zero _) (ne_of_gt gibbsZ_pos)` + `Real.log_exp`。**Phase B 核
  identity の入口**。

### 工数感

~70-90 行 (skeleton + A-1〜A-6)。proof-log: no (Tier 0 baseline、技術的 surprise 想定なし)。

### 失敗時 fallback

- **`stdSimplex` の `mem` 定義 が `Finset.sum` ではなく `Set.indicator` ベースだった場合**:
  inventory §F-1 で確認済 (`{f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}` の素朴形)、unfold で済む。
  万一型不一致なら `show` で展開して bridge。

---

## Phase B — 核 identity + Tier 1 主定理 📋

### スコープ

algebraic identity `klDivPmf_gibbsPmf_eq` (Phase B 全体の重力中心) を取り、Gibbs `klDivPmf_nonneg`
(`CsiszarProjection.lean:61`) と `klDivPmf_self_eq_zero` (`Chernoff.lean:252`) の 2 回呼び出しで
Tier 1 主定理 `entropy_le_gibbs_of_constraints` を合成する。

### Done 条件 (Tier 1 baseline 完成)

- `klDivPmf_gibbsPmf_eq` lemma (核 identity)
- `entropy_le_gibbs_of_constraints` 主定理 0 sorry
- `lake env lean Common2026/Shannon/MaxEntropyConstrained.lean` clean (Phase C / D は sorry 残し可)
- Tier 1 baseline として **そのまま公開可能** な形に到達 (撤退ライン L-S1 trigger 時 close 可)

### ステップ

- [ ] **B-1 核 identity 補題**:
  ```lean
  /-- Algebraic identity: for any Q ∈ stdSimplex on α, the KL from Q to gibbsPmf decomposes
      into entropy + ⟨lam, 𝔼_Q[f]⟩ + log Z(lam). -/
  lemma klDivPmf_gibbsPmf_eq
      {α : Type*} [Fintype α]
      {k : ℕ} (f : Fin k → α → ℝ) (lam : Fin k → ℝ)
      (Q : α → ℝ) (hQ : Q ∈ stdSimplex ℝ α) :
      klDivPmf Q (gibbsPmf f lam)
        = -(∑ x, Real.negMulLog (Q x))
          - (∑ i, lam i * (∑ x, Q x * f i x))
          + Real.log (∑ y, Real.exp (∑ i, lam i * f i y))
  ```
  - 証明 sketch:
    1. `klDivPmf` 定義展開: `∑ x, (gibbsPmf f lam x) * klFun (Q x / gibbsPmf f lam x)`
       — または `CsiszarProjection.klDivPmf` の **sum form 展開済の補題** を在庫 §C で確認
       (`klDivPmf Q gibbs = ∑ x, Q x * (log Q x - log gibbs x)` 形に reshape 可能か Phase B-1
       着手時に loogle で確認)
    2. **直接形 (Mathlib `klFun` を経由しないルート)**: `klDivPmf Q gibbs` を sum form で書き、
       per-term で `Q x * (log Q x - log gibbs x)`、`log gibbs x = ⟨λ,f⟩ - log Z(λ)` (Phase A-6)
       を代入
    3. `Finset.sum_sub_distrib` で 3 項分解: `∑ Q · log Q - ∑ Q · ⟨λ,f⟩ + (∑ Q) · log Z(λ)`
    4. `∑ Q · log Q = -∑ Q · negMulLog`(符号注意、`Real.negMulLog x = -x * Real.log x`)
    5. `∑ Q · ⟨λ,f⟩ = ∑ i, λ i · (∑ x, Q x · f i x)` (`Finset.sum_comm` + 分配)
    6. `(∑ Q) · log Z(λ) = log Z(λ)` (hQ.2 から `∑ Q = 1`)
  - **写経 source**: `DifferentialEntropy.lean:510-660` 内部の Bochner 展開と同モチーフ
    (volume → counting measure, ∫ → ∑)

- [ ] **B-2 Tier 1 主定理**:
  ```lean
  theorem entropy_le_gibbs_of_constraints
      {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
      {k : ℕ} (f : Fin k → α → ℝ) (c : Fin k → ℝ)
      (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
      (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
      (lam : Fin k → ℝ)
      (h_gibbs_constraints : ∀ i, ∑ x, gibbsPmf f lam x * f i x = c i) :
      ∑ x, Real.negMulLog (P x) ≤ ∑ x, Real.negMulLog (gibbsPmf f lam x)
  ```
  - 証明 sketch (4 行核):
    1. `have h_KL : 0 ≤ klDivPmf P (gibbsPmf f lam)` — `klDivPmf_nonneg` (`hP.1` + `gibbsPmf_pos`
       で nonneg 前提を埋める)
    2. `have h_eq_P := klDivPmf_gibbsPmf_eq f lam P hP` — B-1 を Q := P で起動
    3. `have h_self : klDivPmf (gibbsPmf f lam) (gibbsPmf f lam) = 0`
       — `klDivPmf_self_eq_zero (gibbsPmf f lam) gibbsPmf_pos`
    4. `have h_eq_G := klDivPmf_gibbsPmf_eq f lam (gibbsPmf f lam) gibbsPmf_mem_stdSimplex`
       — B-1 を Q := gibbs で起動
    5. `hP_constraints` + `h_gibbs_constraints` で `⟨λ, 𝔼_P[f]⟩ = ⟨λ, c⟩ = ⟨λ, 𝔼_G[f]⟩` 同一視
    6. `linarith` で `H(P) - H(G) = -(klDivPmf P G) - 0 ≤ 0`、つまり `H(P) ≤ H(G)`
  - **設計上のキモ**: `lam` を ansatz として外から取るため、ψ(λ) の凸性 / Lagrange 双対性が
    全く要らない。Tier 1 で完結。

### 工数感

~100-140 行 (B-1 ~70-100 + B-2 ~30-40)。proof-log: **yes** (B-1 算術整理が `Finset.sum_comm` /
`Finset.sum_sub_distrib` の組み合わせで詰まる可能性、写経 source DifferentialEntropy.lean を
精読しながら進める)。

### 失敗時 fallback

- **B-1 で `klDivPmf` の sum form 展開が `klFun` 経由になり頭が痛い** → Phase B-1 の証明を
  `klDivPmf` 定義に直接 unfold せず、**`CsiszarProjection` 既存補題 (`klDivPmf` の sum form
  expression、e.g. `klDivPmf_eq_sum_log_ratio`) を在庫 §C で探す** (loogle で
  `CsiszarProjection.klDivPmf` 系列を再確認)。不在なら **本 plan 内で local private lemma**
  として ~15 行で書き下す。
- **B-2 で `linarith` が立たない (符号反転 / 項抜け)** → `negMulLog` の符号 (`-x * log x`) と
  `klDivPmf` 内部の `klFun` の符号 (`x * log x - x + 1`) を**手計算で照合**してから再挑戦。
  最悪 `nlinarith` / `ring_nf` で代替。
- **B-1 + B-2 で 250 行を超える** → **撤退ライン L-S1 発動**: Tier 1 のみで publish、Phase C
  uniqueness は別 plan に分離。

---

## Phase C — Tier 2 uniqueness 📋

### スコープ

Tier 1 等式バージョン (`entropy_eq_gibbs_iff_of_constraints`) を `csiszar_projection_unique` +
`klDivPmf_strictConvexOn_left` 経路または直接 strict Jensen 経路で証明。

### Done 条件

- `entropy_eq_gibbs_iff_of_constraints` 0 sorry
- (任意) `klDivPmf_eq_zero_iff_pmf` local lemma (`klDivPmf P Q = 0 ↔ P = Q` for full-support Q)
- `lake env lean Common2026/Shannon/MaxEntropyConstrained.lean` clean

### ステップ

- [ ] **C-1 補助 `klDivPmf_eq_zero_iff_pmf`** (full-support Q 限定):
  ```lean
  lemma klDivPmf_eq_zero_iff_pmf
      {α : Type*} [Fintype α]
      {P Q : α → ℝ} (hP : P ∈ stdSimplex ℝ α) (hQ_sum : ∑ a, Q a = 1)
      (hQ_pos : ∀ a, 0 < Q a) :
      klDivPmf P Q = 0 ↔ P = Q
  ```
  - 証明経路 (2 案):
    - **(C-1a) Csiszar 一意性経由**: `K := {Q ∈ stdSimplex | true}` (constraint なし、`stdSimplex`
      全体) で `csiszar_projection_unique` を適用、minimum が Q (`klDivPmf Q Q = 0` is unique min)
      → 任意の `klDivPmf P Q = 0` を持つ P は P = Q。**~25-35 行**。
    - **(C-1b) Strict convexity 直接**: `klDivPmf_strictConvexOn_left Q hQ_pos` + 直接 0-min
      argument (Q が唯一の 0 値点を取る、strict 凸関数の minimum 一意性)。**~20-30 行**。
  - **推奨**: C-1b (より直接的)。在庫 §I で確認した `klDivPmf_strictConvexOn_left`
    (`CsiszarProjection.lean:93`) が `StrictConvexOn ℝ (stdSimplex ℝ α) (fun P => klDivPmf P Q)`
    で、`klDivPmf Q Q = 0` (`klDivPmf_self_eq_zero`) を unique min とする論法。

- [ ] **C-2 主定理 uniqueness**:
  ```lean
  theorem entropy_eq_gibbs_iff_of_constraints
      {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
      {k : ℕ} (f : Fin k → α → ℝ) (c : Fin k → ℝ)
      (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
      (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
      (lam : Fin k → ℝ)
      (h_gibbs_constraints : ∀ i, ∑ x, gibbsPmf f lam x * f i x = c i) :
      ∑ x, Real.negMulLog (P x) = ∑ x, Real.negMulLog (gibbsPmf f lam x)
        ↔ P = gibbsPmf f lam
  ```
  - 証明 sketch:
    1. `(→)` Phase B 主定理 + 等式仮定 → `klDivPmf P (gibbsPmf f lam) = 0` (B-1 identity 経由)
       → C-1 で `P = gibbsPmf f lam`
    2. `(←)` `P = gibbsPmf f lam` 代入で trivially 等式

- [ ] **C-3 代替経路 (任意、Strict Jensen)**:
  `Real.strictConcaveOn_negMulLog` (`Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:224`) +
  `StrictConcaveOn.lt_map_sum` (Mathlib `Analysis/Convex/Jensen.lean:147`) で直接 strict
  Jensen argument。Phase C-1 / C-2 が 100 行を超えたら fallback として検討。
  **本筋では採用しない** (Phase C-1 で十分)。

### 工数感

~50-80 行 (C-1 ~25-35 + C-2 ~25-45)。proof-log: **yes** (C-1b の strict convexity → unique
0-min 論法は Mathlib `StrictConvexOn.eq_of_isMinOn` 系の存在を loogle で確認しながら進める)。

### 失敗時 fallback

- **C-1 で `csiszar_projection_unique` の signature が constraint set `K` を要求**して
  「制約なし版」が綺麗に書けない → C-1b strict convexity 経路に switch (`K := stdSimplex ℝ α`
  全体で 0-min 一意性を取る、~30 行)。
- **C-1b で `StrictConvexOn.eq_of_isMinOn` 系の Mathlib 補題が見つからない** → C-3 strict Jensen
  経路に full switch。本筋から 50 行ほど膨らむが、Tier 2 publish 可能。
- **C-1 + C-2 で 120 行を超える** → **撤退ライン L-S1 発動**: Tier 1 のみで publish、Tier 2
  uniqueness は別 plan `max-entropy-constrained-uniqueness-*` に分離。判断ログに append。

---

## Phase D — 主定理 wrapper + library 編入 📋

### スコープ

主定理 statement の文言整地 (docstring、Tier 1 / Tier 2 の関係、textbook reference) +
`Common2026.lean` 編入 + 仕上げ。

### Done 条件

- `Common2026.lean` に `import Common2026.Shannon.MaxEntropyConstrained` 追記
- `lake env lean Common2026.lean` clean
- 主定理 4 件 (gibbsPmf def / gibbsPmf_mem_stdSimplex / entropy_le_gibbs_of_constraints /
  entropy_eq_gibbs_iff_of_constraints) 全て 0 sorry / 0 warning
- (任意) `chernoff_lemma` 系 + `csiszar_pythagoras_inequality` との cross-link コメント

### ステップ

- [ ] **D-1 docstring 整地**: 各主定理に Cover-Thomas Theorem 12.1.1 reference + Tier 1 / Tier 2
  関係 + Mathlib `Measure.tilted` を使わない理由 (本 plan 判断ログ #1 への pointer) を docstring
  に記載
- [ ] **D-2 `Common2026.lean` 編入**: `import Common2026.Shannon.MaxEntropyConstrained` 追記
- [ ] **D-3 最終 verify**: `lake env lean Common2026.lean` clean 確認 + `Common2026/Shannon/`
  全体回帰チェック (`lake env lean Common2026/Shannon/MaxEntropy.lean` 等が dependent 経由で
  壊れていないか)
- [ ] **D-4 cross-link コメント** (任意): `MaxEntropy.lean` の `entropy_le_log_card` docstring に
  「constraint なし `f = 0` 特例として `entropy_le_gibbs_of_constraints` の系」コメントを追記。
  実装上の再導出は Phase E (stretch)。

### 工数感

~15-25 行 (D-1 docstring ~10 + D-2/3 plumbing ~5 + D-4 任意 ~5)。proof-log: no。

### 失敗時 fallback

- **D-3 で dependent 経由 break** → 該当 file に oleans refresh
  (`lake build Common2026.Shannon.MaxEntropyConstrained` 1 回)。CLAUDE.md "After upstream edits"
  節参照。

---

## Phase E — 特例展開 (Tier 3 stretch) 📋 (任意)

### スコープ

主定理 Tier 2 完成後の **stretch goal**。

### 候補

- [ ] **E-1 Uniform 退化**: `f := 0` (空制約) で `gibbsPmf 0 lam = (1 / Fintype.card α : α → ℝ)`
  (uniform pmf) ↔ `entropy_le_gibbs_of_constraints` から `entropy_le_log_card` 再導出。**既存
  `MaxEntropy.lean` との一致確認**。~30 行。
- [ ] **E-2 2-point exponential**: `α := Bool`, `k := 1`, `f 0 := fun b => if b then 1 else 0`,
  `c := p` で `gibbsPmf` が `Bernoulli(p)` に一致することの確認。教科書 Ex. 12.1 対応。~40 行。
- [ ] **E-3 Discretized exponential**: `α := Fin N`, `f := fun _ x => (x : ℝ)`, `c := μ` で
  `gibbsPmf` が discrete exponential 分布。教科書 Ex. 12.2 対応。~50 行。

### 工数感

各 ~30-50 行。**Tier 2 完成 + judgement ログ追加判断後に着手**。本 plan の必須 scope ではない。

---

## 撤退ライン

### Scope 縮小ライン (発動時に publish 範囲縮退)

- **L-S1**: **Tier 1 (主定理上界) のみで publish** (~200 行)、Tier 2 uniqueness は別 plan に
  - 発動条件:
    - Phase C で `csiszar_projection_unique` の constraint set 翻訳が綺麗に書けない
    - Phase B-1 + B-2 が予想 (140 行) を大幅 (250 行+) に超過
    - Tier 2 が 1 セッションで届かない
  - 縮退後: Tier 1 主定理 (`entropy_le_gibbs_of_constraints`) のみで publish、
    `entropy_eq_gibbs_iff_of_constraints` は別 plan `max-entropy-constrained-uniqueness-*` へ
  - **判断ログに必ず append** + 移行先 plan の seed pointer を本 plan §進捗に追記

- **L-S2**: **Csiszar (B) 経路 fallback** (主 plan の Gibbs 直接 (A) 経路を撤退)
  - 発動条件: Phase B-1 の核 identity `klDivPmf_gibbsPmf_eq` が `klFun` 経由の符号整理で
    100 行+ 詰まる (CsiszarProjection の `klDivPmf` 内部 `klFun` の符号紛れで `linarith` 不発)
  - 縮退後: 制約集合 `K := {Q ∈ stdSimplex | ∀ i, ∑ x, Q x · f i x = c i}` を引数化、
    `csiszar_projection_exists` で `Qstar ∈ K` 存在 + `csiszar_pythagoras_inequality` で
    `klDivPmf P (uniform) ≥ klDivPmf P Qstar + klDivPmf Qstar (uniform)` を取り、
    `Qstar = gibbsPmf f λ` (任意の `λ` で gibbs ∈ K となる ansatz) 同一視で
    `H(P) ≤ H(Qstar) = H(gibbsPmf f λ)` に持ち込む。**追加自作 ~80-120 行**
    (constraint set の closedness/nonempty + Pythagoras 経路)。
  - **本 plan からの違い**: (A) 経路は **algebraic identity 1 本**で Tier 1 を取るが、
    (B) 経路は **Csiszar projection の existence + Pythagoras + ansatz 同一視の 3 段**を要する
    ため 200-300 行重い。よって (A) が動く限り (A) で。

- **L-S3**: **単一制約 `k = 1` 縮退版で publish** (~150 行)
  - 発動条件: Phase B-1 で `Fin k` 走査 (`Finset.sum_comm` + 多変数 `⟨λ,f⟩` 展開) が
    tactic で扱いづらく `k` 一般版が組めない、1 セッション以上の苦戦
  - 縮退後: `k = 1` (`Fin 1` ≃ `Unit`) に縮約、`f : α → ℝ`, `c : ℝ` の **scalar 形** で publish。
    教科書 Ex. 12.1 (Boltzmann factor)、exponential 分布の特例単独。`k` 一般化は別 plan へ。
  - **公開価値**: scalar mean-constraint maximum entropy は教科書頻出の最重要 case で、
    publish 単独でも教科書原稿 (層 3) に組み込み可能。

### 自作 plumbing 肥大ライン (新規)

- **L-P1**: **ψ 凸性 (`log Z(λ)` の `λ` 上での凸性) が主定理に**必要となった場合
  - 発動条件: Phase C uniqueness で `gibbsPmf f λ` 自身の "Lagrange parameter `λ` の一意性"
    まで主張に組み込もうとして、ψ 凸性 + strict 凸性が要請される (本 plan **scope-out**)
  - 縮退案: 「`λ` 一意性は主定理 scope **外**」を改めて確認、判断ログに append、
    主定理は ansatz `λ` を**外から与えられた前提**として閉じる (本 plan の元設計通り)。
    `λ` 存在性 / 一意性は別 seed `max-entropy-constrained-existence-*` 候補。
  - **本 plan の元設計**: ansatz pass-through で ψ 凸性を主定理に組み込まない。L-P1 trigger
    時点で「scope creep を撤退して元設計に戻す」が正しい挙動。

### proof 規模超過ライン

- **L-P2**: **Tier 2 までで 400 行を超える** (親計画上限 400-700 の 400 ライン)
  - 発動条件: Phase A + B + C 合計が 400 行 (中央予測 280 行) を超える
  - 縮退案: L-S1 (Tier 1 単独) 発動。Tier 2 uniqueness の自作 plumbing が膨らんでいる場合
    まず C-1b strict convexity 経路を確認、それでも詰まれば分離。

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| **Phase B-1 核 identity の `klDivPmf` sum-form 展開で `klFun` 符号紛れ** | **中** | 中 (B-1 +20-40 行) | 写経 source `DifferentialEntropy.lean:510-660` の Bochner 展開を**精読してから着手**。`klDivPmf` 内部 `klFun (P x / Q x)` の符号を `P x * (log P x - log Q x) - P x + Q x` 形に bridge する補題が CsiszarProjection に既存なら呼ぶ (在庫 §C で再確認)。`linarith` 不発時は `nlinarith` / `ring_nf` で代替。 |
| **`klDivPmf_self_eq_zero` の hypothesis (`hP_pos`) と `gibbsPmf_pos` の型/名前不一致** | 低 | 低 (1-3 行 plumbing) | Phase A-3 `gibbsPmf_pos` の signature を `klDivPmf_self_eq_zero` (Chernoff.lean:252) の `hP_pos : ∀ a, 0 < P a` と**正確に一致**させる。`gibbsPmf` を pmf 形 (`α → ℝ`) で定義しているので問題なし。 |
| **Phase C で `csiszar_projection_unique` を constraint なし `stdSimplex` 全体に適用しようとして型エラー** | 中 | 中 (C-1 +20 行 or C-1b switch) | C-1b strict convexity 経路に最初から switch。`klDivPmf_strictConvexOn_left` (CsiszarProjection.lean:93) + 0-min 一意性で ~25 行に収まる。 |
| **多変数 `⟨λ, f⟩ = ∑ i, λ i · f i x` の `Finset.sum_comm` 操作が tactic で重い** | 中 | 中 (B-1 +15 行) | `simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_comm]` を `ring_nf` と組み合わせて bulldoze。詰まれば `k` を `Fin 1` に縮退 (撤退ライン L-S3) して scalar 形 publish に逃げる。 |
| **`stdSimplex` の sum form (`∑ x, P x = 1`) が Mathlib では `Finset.sum_eq_one` 系で展開されており destruct が面倒** | 低 | 低 (B-2 +5 行) | `hP.1` (nonneg) と `hP.2` (sum = 1) を冒頭で `obtain ⟨hP_nn, hP_sum⟩ := hP` で分解しておく。 |
| **proof 規模が roadmap 上限 (~280 Tier 2) を超える** | 低-中 | 中 (1 セッションで完走できない) | 撤退ライン L-S1 で Tier 1 単独 publish、Phase C 別 plan 化。Tier 1 baseline ~200 行は 1 セッションで届く想定。 |
| **Phase A で `Real.log_div` の前提 (`分母 ≠ 0`) が gibbs `Z(λ)` の strict positivity から取れない** | 低 | 低 (A-2/A-6 plumbing +3-5 行) | A-2 `gibbsZ_pos` を冒頭で確立 (`Finset.sum_pos` + `Real.exp_pos`、`[Nonempty α]` で `Finset.univ_nonempty`)、A-6 `log_gibbsPmf` で `ne_of_gt gibbsZ_pos` を直接呼ぶ。 |
| **Tier 1 完成後に Tier 2 で `entropy_eq` 形が「`P = gibbsPmf` の点ごと等式」 ↔ 「pmf としての関数等式」の翻訳で詰まる** | 低 | 低 (C-2 +5 行) | `funext x` で各 `x` の等式に下ろし、Phase A-3 + A-4 (gibbs の各点 strict positivity + 和 = 1) と Tier 1 sum 等式の per-term 比較で帰着。strict convexity (C-1b) の 0-min 一意性が pmf 関数等式を直接吐く想定。 |

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(2026-05-19) KKT / Lagrange duality を採用しない**: 在庫調査
   (`max-entropy-constrained-mathlib-inventory.md`) で「Mathlib KKT 不在
   (`LagrangeMultipliers.lean:22-24` で TODO 明記)」を確認。Lagrange API は存在
   (`IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt`) するが、entropy の
   `HasStrictFDerivAt` を `stdSimplex` の境界で取る議論が +150 行膨らむ。これに対し
   **`Measure.tilted` を pmf 形 `gibbsPmf` で書き直し + Csiszar `klDivPmf ≥ 0` + 算術
   identity の 3 段** で Tier 1 主定理が ~200 行で取れる (Mathlib-shape-driven、CLAUDE.md
   ルール準拠)。**親計画の "Lagrange 双対性 + KKT" 撤退ラインは発動なし**。

2. **(2026-05-19) ansatz `λ` を主定理 signature の hypothesis として外から取る (pass-through 設計)**:
   主定理 `entropy_le_gibbs_of_constraints` の signature で `lam : Fin k → ℝ` と
   `h_gibbs_constraints : ∀ i, ∑ x, gibbsPmf f lam x * f i x = c i` を**呼び出し側の責務**として
   外から要求する。これにより:
   - ψ(λ) の凸性 (Mathlib `cgf_convex` 不在、自作 ~50 行) が主定理 scope 外
   - Lagrange parameter `λ` の存在性 (実装には逆関数定理 / Banach 固定点 / 凸双対が必要、
     Mathlib 整備不十分) が主定理 scope 外
   - 教科書 12.1.1 の "Lagrange 解析" を**完全に回避**し、主張は「制約を満たす ansatz が
     与えられたとき、その gibbs が最大化元」という**条件付き形**に
   将来 `λ` 存在性 / 一意性を別 seed `max-entropy-constrained-existence-*` で扱う想定。
   本 plan で主張する `H(P) ≤ H(gibbsPmf f λ)` は ansatz `λ` を任意に取れるため、
   実用上「適切な `λ` を見つけて代入」する形で textbook 12.1 の結論を full に再現可能。

3. **(2026-05-19) 規模見積を親計画 400-700 → ~280 (Tier 2) に再評価**: 在庫調査で Csiszar pmf
   経路 + Mathlib `Real.exp/log/rpow` 算術 + DifferentialEntropy.lean Phase D 写経 source の
   3 点で「親計画見積もりは Mathlib `tilted` + Csiszar projection の既存度を見落としていた」
   と判定。**Tier 1 baseline ~200 行 / Tier 2 ~280 行 / Tier 3 stretch ~350-400 行**で段階的
   publish 設計。1 セッション目標を **Tier 1 (~200 行)** とし、Tier 2 が同セッションで届かなければ
   judgement 4 で追記して別 plan 分離 (撤退ライン L-S1)。

4. **(2026-05-19) Tier 2 を 1 セッションで完成、撤退ライン非発動**: 実装で `MaxEntropyConstrained.lean`
   = 361 行 (見積もり 280 行に対して +30%)。撤退ライン L-S1〜L-P2 はいずれも非発動。
   - Phase A (Tier 0) は ~80 行で予想通り (Phase A-1 で `gibbsZ` を独立 `def` 化したことで Phase B-1
     の `log Z(λ)` 参照が直線化)。
   - Phase B-1 (核 identity `klDivPmf_gibbsPmf_eq`) が ~90 行で本ファイル最大の重力中心。`klFun` 内部
     展開 (`Q a * klFun (P a / Q a) = -negMulLog (Q a) + ... + gibbs - Q a`) を `Q a = 0` ⁄ `Q a > 0`
     で場合分けし、`field_simp` で per-term 整理、`Finset.sum_comm` + `Finset.mul_sum` で多変数
     `⟨λ, 𝔼_Q[f]⟩` 形に reshape。Risk table の「`Finset.sum_comm` 操作が tactic で重い」が実際 ~10 行
     plumbing で吸収できた (撤退ライン L-S3 `k = 1` 縮退は不発)。
   - Phase B-2 (Tier 1 主定理) は B-1 を Q := P, Q := gibbs で 2 回呼ぶ + `linarith` 4 行核で ~35 行。
     ansatz pass-through 設計 (判断ログ #2) が機能、Lagrange parameter `λ` の凸性 / 存在性は完全 scope-out。
   - Phase C-1 (`klDivPmf_eq_zero_iff_pmf`) は **strict convexity 経路 (C-1b) ではなく、`klFun ≥ 0`
     per-term ⇒ `klFun_eq_zero_iff` 直接ルート**で書けた (~35 行)。
     - `klDivPmf P Q = ∑ Q a * klFun (P a / Q a) = 0` で per-term ≥ 0 → 全項 0 → `klFun (P a / Q a) = 0`
       (Q a > 0 なので) → `P a / Q a = 1` (`klFun_eq_zero_iff`) → `P a = Q a`。
     - 計画では C-1a (`csiszar_projection_unique` 経由) / C-1b (`klDivPmf_strictConvexOn_left` 経由) を
       検討していたが、**Mathlib `klFun_eq_zero_iff` (`KLFun.lean:151`) を per-term 適用する方が直接的**
       で ~30 行で済む。strict convexity への依存ゼロ。
   - Phase C-2 (Tier 2 uniqueness) は B-1 identity 再利用 + C-1 + `linarith` で ~40 行。
   - Phase D は `Common2026.lean` への import 行 1 行追加のみ (docstring は最初から書いてある)。
   - 全体として「**最初の手筋 (Gibbs + Csiszár `klDivPmf` pmf 直接ルート + ansatz pass-through)
     で 0 sorry / 0 warning に到達**」。**Phase E (Tier 3 特例展開) は本セッション 未着手、別 plan で対応想定**。
