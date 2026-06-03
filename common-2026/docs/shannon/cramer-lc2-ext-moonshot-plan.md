# Cramér L-C2 extension ムーンショット計画 🌙 (T1-C follow-up extension)

> 実態整合 (2026-05-20): **DONE-HONEST-HYPS (Phase A'+B-1+B-3 完遂)** — 計画通り完了。
> `InformationTheory/Shannon/CramerLC2DischargeExt.lean` (0 sorry) に全 publish 済: Phase A' bypass 補題
> `isProbabilityMeasure_infinitePi_tilted_of_bounded` (:85) / `pairwise_indepFun_tilted_ambient` (:99) /
> `integrable_eval_under_infinitePi_tilted` (:111) / `integral_eval_under_infinitePi_tilted` (:132)、
> Phase B-1 `tilted_lln_ae` (:165)、Phase B-3 `tilted_lln_in_probability` (:205) + `.real` 形 corollary
> `tilted_lln_in_probability_real` (:236)。Phase C (change-of-measure) は予告どおり scope 外だが後継
> `infinitepi-tilted` plan で discharge 済。**進捗 Phase 0-V が全 [ ] のままだが実態は全完了。**

> **Parent**: [`cramer-lc2-discharge-moonshot-plan.md`](cramer-lc2-discharge-moonshot-plan.md) (Phase A まで publish 済、Phase B-C が L-D3 撤退状態)
>
> **Predecessor (publish)**: `InformationTheory/Shannon/CramerLC2Discharge.lean` (171 行、Phase A tilted IID plumbing 6 補題)
>
> **Status (2026-05-20)**: 着手前。`cramer-lc2-discharge` の Phase A は完了済 (`CramerLC2Discharge.lean`)。Phase B `strong_law_ae_real` 起動は前セッションで「`IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => μ₀.tilted ...))` の typeclass synthesis が beta-reduction で詰まる」という構造的障害で defer された。本 plan はその障害を **bypass 補題** で迂回し、Phase B (tilted LLN 起動 + in-probability 化) を publish する。
>
> **Approach 採用**: **option (c)** — `Measure.infinitePi_const_isProbabilityMeasure` を local statement で書いて beta-redex bypass し、Phase B (LLN + in-probability) を独立 publish。Phase C (`cramer_lower_discharged` 完全 discharge) は依然として change-of-measure n-letter 化 (`Measure.infinitePi (fun _ => μ.tilted ...) = (Measure.infinitePi μ).tilted (∑ ...)` の Mathlib 不在) で詰まるため、本 plan の scope 外とし `(b)/(c)` 縮退で着地。
>
> **撤退ライン**: [L-E1] Phase B-3 (`tendstoInMeasure_of_tendsto_ae` 起動) のシグナル変換が無理なら、Phase B-1 (a.s. LLN 起動のみ) で着地。[L-E2] それも詰まれば、beta-redex bypass 補題群 (`isProbabilityMeasure_infinitePi_tilted_of_bounded`、`pairwise_indepFun_tilted_ambient`、`integrable_eval_under_infinitePi`) のみ publish (~150 行)。

## 進捗

- [ ] Phase 0 — `IsProbabilityMeasure (Measure.infinitePi const)` 直撃 + 既存 Phase A 補題の signature 再確認 📋
- [ ] Phase A' — beta-redex bypass 補題群 (typeclass synthesis 詰まり解消) 📋
- [ ] Phase B-1 — Mathlib `strong_law_ae_real` を tilted ambient で起動 📋
- [ ] Phase B-3 — a.s. LLN → in-probability LLN 変換 (`tendstoInMeasure_of_tendsto_ae`) 📋
- [ ] Phase V — verify + 親 plan の Phase B 状態反映 📋

## ゴール / Approach

### Goal (最終定理 signature 群)

`InformationTheory/Shannon/CramerLC2DischargeExt.lean` (新規) で以下を publish:

```lean
-- Phase A' (Mathlib PR-candidate, beta-redex bypass)
lemma isProbabilityMeasure_infinitePi_tilted_of_bounded
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    IsProbabilityMeasure
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) := …

lemma pairwise_indepFun_tilted_ambient
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    Pairwise ((· ⟂ᵢ[Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))] ·)
      on (fun (i : ℕ) (ω : ℕ → Ω₀) => Y (ω i))) := …

lemma integrable_eval_under_infinitePi_tilted
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    Integrable (fun ω : ℕ → Ω₀ => Y (ω 0))
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) := …

-- Phase B-1 (a.s. LLN on tilted ambient)
theorem tilted_lln_ae
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)),
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, Y (ω i)) / n) atTop
        (𝓝 ((μ₀.tilted (fun ω => lam * Y ω))[Y])) := …

-- Phase B-3 (in-probability LLN, via tendstoInMeasure_of_tendsto_ae)
theorem tilted_lln_in_probability
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    TendstoInMeasure
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)))
      (fun n ω => (∑ i ∈ Finset.range n, Y (ω i)) / n)
      atTop
      (fun _ => (μ₀.tilted (fun ω => lam * Y ω))[Y]) := …
```

### Approach (overall strategy / shape of solution)

**戦略の shape**: 前セッションは Phase B 起動時に Lean の typeclass synthesis が

```lean
∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ => μ₀.tilted (lam * Y ·)) i)
```

の `i` への β-redex を展開せず、`Measure.infinitePi` 標準 instance (`[hμ : ∀ i, IsProbabilityMeasure (μ i)]`) と unify できない問題で詰まった (cf. `CramerLC2Discharge.lean` docstring §Status)。

本 plan は **3 段で迂回**:

```
Phase A' (bypass 補題 publish):
  ├─ isProbabilityMeasure_infinitePi_tilted_of_bounded
  │    haveI を補題内部で隠蔽し、外部から見ると Cramér-specific な
  │    具体 type の `IsProbabilityMeasure` 主張として直接書く。これは
  │    Mathlib `Measure.infinitePi` instance + tilted prob (既存 Phase A
  │    の `isProbabilityMeasure_tilted_of_bounded`) を `haveI` で集めて
  │    1 行で抜くだけだが、外向き lemma にすることで callsite で β 展開を
  │    気にする必要が消える (= Lean に明示の term を渡せる)
  │
  ├─ pairwise_indepFun_tilted_ambient
  │    既存 `iIndepFun_tilted_ambient` + Mathlib `iIndepFun.indepFun`
  │    格下げ。`Pairwise ((· ⟂ᵢ[μ_lam^∞] ·) on Y)` の形で書く。
  │
  └─ integrable_eval_under_infinitePi_tilted
       bounded RV + IsProbabilityMeasure ⇒ `Integrable Y₀ μ_lam^∞`。
       既存 `bounded_eval_family` + `integrable_const.mono'` で 10 行。

       ↓ (Phase A' 完了で Mathlib `strong_law_ae_real` の 3 前提が揃う)

Phase B-1 (a.s. LLN 起動):
  ├─ tilted_lln_ae
  │    strong_law_ae_real (fun i ω => Y (ω i)) hint hindep hident
  │    で 1 行 (実質 4-5 行のラッパー)。
  │
  │    結論の右辺 `μ[X 0]` = tilted ambient 上の `Y ∘ eval 0` の積分
  │    = (Mathlib `infinitePi_map_eval` + `integral_map`) = tilted base
  │      の `Y` の積分 = `(μ₀.tilted (lam * Y ·))[Y]`.
  │
  │    `integral_eval_under_infinitePi_tilted` helper で右辺式を整える。

       ↓ (a.s. → in-probability)

Phase B-3 (in-probability 化):
  └─ tilted_lln_in_probability
       Mathlib `tendstoInMeasure_of_tendsto_ae` を起動。
       前提: `IsFiniteMeasure` (= IsProbabilityMeasure から) + ∀ n, AEStronglyMeasurable.
       右辺: 定数函数 `fun _ => (μ₀.tilted ...)[Y]`、これは
         `aestronglyMeasurable_const`.
```

**核心**: Phase A' は β-redex bypass のための「外向き lemma」化、新数学はゼロ。前セッションの Phase A プルーフはすでに `haveI` を 2 段書いて beta-reduction を意図的に通している (`CramerLC2Discharge.lean:90-91` で `haveI : ∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)) i) := fun _ => hp`)。本 plan ではこれを **再利用可能な定理 wrapper** に昇格させる。

**Mathlib-shape-driven**: `strong_law_ae_real` の結論 `μ[X 0] := ∫ x, X 0 x ∂μ` は `Measure.infinitePi (fun _ => μ₀.tilted ...)` 側で評価される。これを `(μ₀.tilted ...)[Y]` に bridge するための `integral_eval_under_infinitePi_tilted` も補題化（既存 Phase A `identDistrib_tilted_ambient` の `map_eq` から push-forward の `integral_map` 一本）。

**Phase C (change-of-measure) を scope-out した根拠**: Phase C の中核は

```lean
(Measure.infinitePi (fun _ => μ₀)).tilted (∑ i ∈ Finset.range n, lam * Y (ω i))
  = ? (= Measure.infinitePi (fun _ => μ₀.tilted (lam * Y ·))) のうち range n の部分のみ
```

の同定。これは Mathlib に直接 lemma がなく、`rnDeriv` の n-letter 形を **手で構築する必要** がある (cf. 親 plan §C-1)。500-1000 行 scope で本 seed の 1 セッション完遂とは整合しない。本 plan の Phase B publish で「tilted side LLN」を確立し、後続 plan (`cramer-change-of-measure-discharge-plan.md`) で change-of-measure を独立扱いする方針が自然。

### 規模見積もり (中央予測)

| 自作要素 | 想定行数 | Phase |
|---|---|---|
| skeleton + imports + docstring | ~30 | A' |
| `isProbabilityMeasure_infinitePi_tilted_of_bounded` | ~10-15 | A' |
| `pairwise_indepFun_tilted_ambient` | ~15-25 | A' |
| `integrable_eval_under_infinitePi_tilted` | ~25-40 | A' |
| `integral_eval_under_infinitePi_tilted` (bridge) | ~30-50 | A' |
| `tilted_lln_ae` | ~30-50 | B-1 |
| `tilted_lln_in_probability` | ~30-50 | B-3 |
| `tilted_lln_in_probability_real` (`μ.real` 形 corollary) | ~15-25 | B-3 |
| **合計** | **~185-285 行** | |

中央予測 **~230 行**。seed 制約 (~150-400 行) 内。

### ファイル構成

`InformationTheory/Shannon/CramerLC2DischargeExt.lean` 新規 (`CramerLC2Discharge.lean` を import、再エクスポートなしの素朴 publish)。

## Phase 0 — Mathlib API 再確認 📋

### スコープ

以下の signature を `file:line` + 完全前提リスト verbatim で record:

1. `Mathlib/Probability/ProductMeasure.lean:378` の `instance : IsProbabilityMeasure (Measure.infinitePi μ)` の 前提 `[hμ : ∀ i, IsProbabilityMeasure (μ i)]`
2. `Mathlib/Probability/StrongLaw.lean:598` の `strong_law_ae_real`
3. `Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:223` の `tendstoInMeasure_of_tendsto_ae`
4. `Mathlib/Probability/Independence/Basic.lean:447` の `iIndepFun.indepFun`

### Done 条件

- 上記 4 件の signature を本 plan に inline 記録
- Phase A' skeleton が書ける状態

## Phase A' — beta-redex bypass 補題群 📋

### スコープ

`CramerLC2Discharge.lean:90-91` の `haveI : ∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)) i) := fun _ => hp` パターンを外向き lemma に昇格。新規 3 件 (+1 bridge):

- `isProbabilityMeasure_infinitePi_tilted_of_bounded` (~10 行)
- `pairwise_indepFun_tilted_ambient` (~20 行)
- `integrable_eval_under_infinitePi_tilted` (~30 行)
- `integral_eval_under_infinitePi_tilted` (push-forward 経由の bridge、~40 行)

### Done 条件

- 4 補題が `lake env lean` clean
- 既存 `CramerLC2Discharge.lean` の Phase A 補題と signature 整合

## Phase B-1 — a.s. LLN on tilted ambient 📋

### スコープ

Phase A' で揃えた 3 前提を `strong_law_ae_real` に渡す。`tilted_lln_ae` 1 件 publish。

### Done 条件

- `tilted_lln_ae` が `lake env lean` clean

## Phase B-3 — in-probability LLN on tilted ambient 📋

### スコープ

`tendstoInMeasure_of_tendsto_ae` 起動。`tilted_lln_in_probability` 1 件 + `.real`-形 corollary 1 件 publish。

### Done 条件

- 両定理が `lake env lean` clean

## Phase V — verify + 親 plan 反映 📋

### スコープ

- `lake env lean InformationTheory/Shannon/CramerLC2DischargeExt.lean` clean
- 親 plan `cramer-lc2-discharge-moonshot-plan.md` の Phase B 進捗を 🔄 → 🟡 (B-1 + B-3 部分達成) に更新
- `InformationTheory.lean` に `import InformationTheory.Shannon.CramerLC2DischargeExt` 追記

### 後継 plan 候補

- `cramer-change-of-measure-discharge-plan.md` (Phase C 本体 = change-of-measure n-letter 化 + RN deriv 構築、~500-1000 行、独立 seed)

## 判断ログ

1. **2026-05-20 起草**: 前セッション (cf. `cramer-lc2-discharge-moonshot-plan.md` §判断ログ #1) の typeclass synthesis 詰まりを bypass する scope 縮退形 plan として起草。option (a) (`Measure.infinitePi_const_isProbabilityMeasure` 局所定理) を採用、option (b) (Sanov 経由) は親 plan 既に却下、option (c) (Phase A 追補) は本 plan で Phase A' という形で吸収。Phase C (change-of-measure) は scope-out。
