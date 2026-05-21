# Chernoff converse — band-mass discharge Mathlib 在庫調査

> 対象: `Common2026/Shannon/ChernoffSanovDischarge.lean` の honest load-bearing 仮説
> `IsChernoffBandMassToOne` (`:243`) を genuine に discharge するための Mathlib インフラ調査。
> 親計画: [`chernoff-converse-sanov-discharge-plan.md`](chernoff-converse-sanov-discharge-plan.md)
> (撤退ライン L-SD1 / L-SD2)。同種文書: [`chernoff-mathlib-inventory.md`](chernoff-mathlib-inventory.md)。
>
> 調査日 2026-05-21。実装・計画起草はしない。

## 一行サマリ

**GO**。discharge に使う API のうち実体は **約 90% 既存**。(b) Q-LLN は SLLN
(`strong_law_ae_real`) + 無限積上の coordinate IID (`iIndepFun_infinitePi`) + a.s.→確率収束
(`tendstoInMeasure_of_tendsto_ae`) が**全部揃っており**、しかも本プロジェクトに**そっくりな
plumbing template** (`CramerLC2Discharge.iIndepFun_eval_under_infinitePi` /
`identDistrib_eval_under_infinitePi`) が既存。(a) 一次最適性は `λ↦c^λ` の微分
(`Real.hasStrictDerivAt_const_rpow`) + Fermat (`IsLocalMin.hasDerivAt_eq_zero`) +
interior (`interior_Icc`) で組める。**自作必要は 5 件、すべて plumbing/接続**で genuine な
Mathlib gap はゼロ。**撤退ライン L-SD1 は発動しない**(`Measure.pi`/`infinitePi` の coordinate
独立→`IndepFun` 橋は Mathlib に実在)。最大の注意点 2 件: **(i) 境界ケース `λ*∈{0,1}` の
case-split が必須**(内点一次条件が崩れる; ただし `Z(0)=Z(1)=1` から `chernoffInfo=0` で別処理可)、
**(ii) `Fin n` 添字 (band) ↔ `ℕ`/`Finset.range n` 添字 (SLLN/infinitePi) の reindex plumbing**。

---

## 主定理の最終形 (再掲)

discharge 対象 (`ChernoffSanovDischarge.lean:243`):

```lean
def IsChernoffBandMassToOne (P₁ P₂ : α → ℝ) (lam : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (1 / 2 : ℝ)
      ≤ ∑ x ∈ (chernoffLogRatioBand P₁ P₂ n ε).toFinite.toFinset,
          ∏ i, ChernoffConverse.chernoffMediator P₁ P₂ lam (x i)
```

discharge した暁の headline (現状 `chernoff_converse_of_bandMass`, `:457` がこの仮説を取る):

```lean
-- 目標: 仮説 IsChernoffBandMassToOne を外した genuine 版
theorem chernoff_band_mass_to_one_of_interior_optimal
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (hlam_int : lam ∈ Set.Ioo (0:ℝ) 1)
    (hlam_min : IsMinOn (fun l => chernoffZSum P₁ P₂ l) (Set.Icc 0 1) lam) :
    IsChernoffBandMassToOne P₁ P₂ lam
```

証明戦略 (pseudo-Lean):
```text
-- (a) 一次最適性: Z は λ で微分可能 (各項 c^λ の HasDerivAt.sum)
have hZ' : HasDerivAt (Z) (∑ a, T(a)·(log P₁ a − log P₂ a)) lam   -- const_rpow×const_rpow.mul.sum
have : IsLocalMin Z lam := hlam_min.isLocalMin (interior_Icc ▸ hlam_int の近傍性)
have h_fermat : (∑ a, T(a)·(log P₁ a − log P₂ a)) = 0           -- IsLocalMin.hasDerivAt_eq_zero
-- ⇒ Q-mean of (log P₁ − log P₂) = 0,  Q = chernoffMediator
-- (b) Q-LLN: infinitePi Q^∞ 上で eval が iIndepFun + IdentDistrib (template 流用)
have h_slln : ∀ᵐ ω ∂(infinitePi Q), Tendsto (emp mean) atTop (𝓝 (Q-mean = 0))  -- strong_law_ae_real
have h_inmeas : TendstoInMeasure (infinitePi Q) (emp mean) atTop 0             -- tendstoInMeasure_of_tendsto_ae
-- ⇒ band complement mass → 0 ⇒ band mass ≥ 1/2 eventually
-- (c) infinitePi band-mass ↔ Measure.pi (Fin n) ↔ ∑∏ chernoffMediator
--     (infinitePi_map_restrict + chernoffMediatorMeasure_pi_singleton_toReal + reindex)
```

---

## API 在庫テーブル

CLAUDE.md「Subagent Inventory of Mathlib Lemmas」規定: `file:line` / 完全 signature
(`[...]` typeclass prereq verbatim) / 引数型 / 結論形 verbatim。

### A. (a) 一次最適性 — `λ ↦ Z(λ)` の微分 (`Real.rpow` 指数微分)

| 概念 | Mathlib API | file:line | 状態 | discharge での扱い |
|---|---|---|---|---|
| `λ↦a^λ` の strict 微分 | `Real.hasStrictDerivAt_const_rpow` | `Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean:401` | 既存 | **各項微分の主役** |
| `λ↦a^(f λ)` の微分 (合成) | `HasDerivAt.const_rpow` | `Pow/Deriv.lean:728` | 既存 | `1-λ` 指数項 (`f λ = 1-λ`) に使用 |
| `deriv (λ↦a^(f λ))` | `deriv_const_rpow` | `Pow/Deriv.lean:742` | 既存 | `deriv` 形が必要なとき |
| 積の微分 | `HasDerivAt.mul` | `Mathlib/Analysis/Calculus/Deriv/Mul.lean` | 既存 | `(P₁ a)^(1-λ)·(P₂ a)^λ` の積 |
| 有限和の微分 | `HasDerivAt.sum` | `Mathlib/Analysis/Calculus/Deriv/Add.lean` | 既存 | `Z = ∑_a (項)` |

`Real.hasStrictDerivAt_const_rpow` 結論形 verbatim:
```
theorem hasStrictDerivAt_const_rpow {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasStrictDerivAt (fun x => a ^ x) (a ^ x * log a) x
```
引数: `{a : ℝ}` (暗黙), `(ha : 0 < a)`, `(x : ℝ)`。typeclass prereq なし。
`HasDerivAt.const_rpow` 結論形 verbatim (context: `{f : ℝ → ℝ} {f' x : ℝ} {a : ℝ}`):
```
theorem HasDerivAt.const_rpow (ha : 0 < a) (hf : HasDerivAt f f' x) :
    HasDerivAt (a ^ f ·) (Real.log a * f' * a ^ f x) x
```
→ 各項 `(P₁ a)^(1-λ)·(P₂ a)^λ` の `λ`-微分は
`= 項·(log(P₂ a) − log(P₁ a))`。和で `Z'(λ) = ∑_a 項·(log P₂ − log P₁) = −Z(λ)·E_Q[log P₁ − log P₂]`
(`項 = Z·chernoffMediator`)。`Z'(λ*) = 0 ⇔ E_Q[log P₁ − log P₂] = 0`。

### B. (a) 内点最小 → 一次条件 0 (Fermat)

| 概念 | Mathlib API | file:line | 状態 | discharge での扱い |
|---|---|---|---|---|
| 局所最小で微分 0 (HasDerivAt 形) | `IsLocalMin.hasDerivAt_eq_zero` | `Mathlib/Analysis/Calculus/LocalExtr/Basic.lean:237` | 既存 | **一次条件の主役** |
| 局所最小で `deriv = 0` | `IsLocalMin.deriv_eq_zero` | `LocalExtr/Basic.lean:241` | 既存 | `deriv` 形代替 |
| 集合最小 → 局所最小 (近傍) | `IsMinOn.isLocalMin` | `Mathlib/Topology/Order/LocalExtr.lean:143` | 既存 | `Icc`-min → interior local min |
| `interior (Icc a b) = Ioo a b` | `interior_Icc` | `Mathlib/Topology/Order/DenselyOrdered.lean:122` | 既存 | `λ*∈Ioo` の近傍性供給 |
| compact 上 min 達成 (`IsMinOn` 出力) | `IsCompact.exists_isMinOn` | `Mathlib/Topology/Order/Compact.lean` | 既存 | **`IsMinOn` witness を出す** (下記注) |

`IsLocalMin.hasDerivAt_eq_zero` 結論形 verbatim (context: `{f : ℝ → ℝ} {f' a : ℝ}`):
```
theorem IsLocalMin.hasDerivAt_eq_zero (h : IsLocalMin f a) (hf : HasDerivAt f f' a) : f' = 0
```
`IsMinOn.isLocalMin` 結論形 verbatim (context: `{f : α → β} {s : Set α} {a : α}` 順序位相):
```
theorem IsMinOn.isLocalMin (hf : IsMinOn f s a) (hs : s ∈ 𝓝 a) : IsLocalMin f a
```
`interior_Icc` 結論形 verbatim:
```
theorem interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : interior (Icc a b) = Ioo a b
```
**注 — `chernoffInfo_attained` の弱さ**: 既存 `chernoffInfo_attained` (`Chernoff.lean:163`) は
`IsCompact.exists_sInf_image_eq` 経由で `∃ λ∈Icc, chernoffInfo = -log Z(λ)` のみ供給し、
**`IsMinOn` witness を露出しない**。一次最適性には `IsMinOn (Z or log∘Z) (Icc 0 1) λ*` が要る。
`IsCompact.exists_isMinOn` で `IsMinOn` 付き達成点を取り直す補助補題が要る (下記自作 #1)。

### C. (b) Q-LLN — 大数の法則 (a.s.)

| 概念 | Mathlib API | file:line | 状態 | discharge での扱い |
|---|---|---|---|---|
| **SLLN (実数 iid)** | `ProbabilityTheory.strong_law_ae_real` | `Mathlib/Probability/StrongLaw.lean:598` | 既存 | **Q-LLN の主役** |
| SLLN (Banach 空間, integrable) | `ProbabilityTheory.strong_law_ae` | `StrongLaw.lean:788` | 既存 | 不要 (実数版で足りる) |

`strong_law_ae_real` 完全 signature verbatim:
```
theorem strong_law_ae_real {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ i ∈ range n, X i ω) / n) atTop (𝓝 μ[X 0])
```
引数: `(X : ℕ → Ω → ℝ)`, `(hint : Integrable (X 0) μ)`,
`(hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))` ← **pairwise** independence で十分 (Etemadi),
`(hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)`。
**typeclass prereq: なし** (`IsProbabilityMeasure` すら不要; 内部で `hint`+`hindep` から導出)。
**前提事故ポイント**:
- 結論の和は **`∑ i ∈ range n` (Finset.range n ⊂ ℕ)**、band の `∑ i : Fin n` と添字が**違う**
  (reindex plumbing 要、下記自作 #4)。
- 極限値は `μ[X 0]` = `X 0` の積分。`X i ω := log P₁(ω i) − log P₂(ω i)`,
  `μ := infinitePi (fun _ => Q)` のとき `μ[X 0] = E_Q[log P₁ − log P₂]`。一次最適性で `= 0`。
- 弱法則 (weak law / "in probability" 専用版) は **Mathlib に名前として不在**
  (`"weak_law"` / `"law_of_large"` 検索 0 件)。**a.s.→確率収束で代替** (下記 D)。

### D. (b) a.s. 収束 → 確率収束 (band complement mass → 0)

| 概念 | Mathlib API | file:line | 状態 | discharge での扱い |
|---|---|---|---|---|
| **a.s.→確率収束** | `MeasureTheory.tendstoInMeasure_of_tendsto_ae` | `Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:223` | 既存 | **band mass→1 の橋** |
| 確率収束 定義 | `MeasureTheory.TendstoInMeasure` | `ConvergenceInMeasure.lean:57` | 既存 | `μ{ε≤edist}→0` を直接供給 |
| edist 版測度収束 (前段) | `tendstoInMeasure_of_tendsto_ae_of_measurable_edist` | `ConvergenceInMeasure.lean:202` | 既存 | 補助 |

`TendstoInMeasure` 定義 verbatim:
```
def TendstoInMeasure [EDist E] {_ : MeasurableSpace α} (μ : Measure α) (f : ι → α → E)
    (l : Filter ι) (g : α → E) : Prop :=
  ∀ ε, 0 < ε → Tendsto (fun i => μ { x | ε ≤ edist (f i x) (g x) }) l (𝓝 0)
```
`tendstoInMeasure_of_tendsto_ae` 結論形 verbatim
(context: `{f : ℕ → α → E} {g : α → E}`; `E` は metric 系):
```
theorem tendstoInMeasure_of_tendsto_ae [IsFiniteMeasure μ]
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    TendstoInMeasure μ f atTop g
```
**typeclass prereq: `[IsFiniteMeasure μ]`** ← `infinitePi Q` は確率測度なので OK
(`Measure.instIsProbabilityMeasureForallInfinitePi` 自動)。`AEStronglyMeasurable` は有限 `α` で自明。
→ `f n ω := (∑ i∈range n, X i ω)/n`, `g := const 0`, ε で `μ{|emp mean|≥ε}→0`
⇒ band 補集合 mass → 0 ⇒ band mass → 1 ≥ 1/2 eventually。

### E. (b) 無限積上の coordinate IID 供給 (撤退ライン L-SD1 の核心)

| 概念 | Mathlib API | file:line | 状態 | discharge での扱い |
|---|---|---|---|---|
| **無限積上 coordinate iIndepFun** | `ProbabilityTheory.iIndepFun_infinitePi` | `Mathlib/Probability/Independence/InfinitePi.lean:103` | 既存 | **L-SD1 を不発にする鍵** |
| iIndepFun → pairwise IndepFun | `ProbabilityTheory.iIndepFun.indepFun` | `Mathlib/Probability/Independence/Basic.lean:447` | 既存 | SLLN の `Pairwise ⟂ᵢ` 供給 |
| 有限積 coordinate iIndepFun | `ProbabilityTheory.iIndepFun_pi` | `Independence/Basic.lean:784` | 既存 | **`[Fintype ι]` 制約あり** (下記注) |
| coordinate eval の law = μ | `MeasureTheory.Measure.infinitePi_map_eval` | `Mathlib/Probability/ProductMeasure.lean` | 既存 | IdentDistrib の `map_eq` 供給 |
| IdentDistrib 構造 | `ProbabilityTheory.IdentDistrib` | `Mathlib/Probability/IdentDistrib.lean:71` | 既存 | `map_eq` フィールドで構成 |

`iIndepFun_infinitePi` 完全 signature verbatim
(context: `variable {ι Ω : Type*} ... {𝓧 : ι → Type*} [∀ i, MeasurableSpace (𝓧 i)]`):
```
lemma iIndepFun_infinitePi {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
    {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)] {X : (i : ι) → Ω i → 𝓧 i}
    (mX : ∀ i, Measurable (X i)) :
    iIndepFun (fun i ω ↦ X i (ω i)) (infinitePi P)
```
**typeclass prereq: `[∀ i, IsProbabilityMeasure (P i)]`**。**`ι` に `[Fintype ι]` 制約なし**
→ `ι = ℕ` で動く ← **これが決定的**。`chernoffMediatorMeasure` は
`chernoffMediatorMeasure_isProbabilityMeasure` (`ChernoffPerTiltDischarge.lean:435`) で確率測度。
`iIndepFun.indepFun` 結論形 verbatim:
```
theorem iIndepFun.indepFun {β : ι → Type*}
    {m : ∀ x, MeasurableSpace (β x)} {f : ∀ i, Ω → β i} (hf_Indep : iIndepFun f μ) {i j : ι}
    (hij : i ≠ j) :
    f i ⟂ᵢ[μ] f j
```
**注 — `iIndepFun_pi` は `[Fintype ι]` 必須**: `Independence/Basic.lean:778` の
`variable {ι : Type*} [Fintype ι]`。SLLN は `ℕ`-indexed (無限) なので `iIndepFun_pi` は
使えず、**`iIndepFun_infinitePi` (Fintype 不要) が必須**。→ Q-LLN は `Measure.pi (Fin n)` でなく
`infinitePi Q` 上で走らせ、最後に `Fin n` 形へ橋渡す (下記 F + 自作 #4)。

### F. (b)→(c) 無限積 band-mass ↔ pmf 形 `∑∏ chernoffMediator` の橋

| 概念 | Mathlib API | file:line | 状態 | discharge での扱い |
|---|---|---|---|---|
| `infinitePi` の Finset 制限 = `Measure.pi` | `MeasureTheory.Measure.infinitePi_map_restrict` | `Mathlib/Probability/ProductMeasure.lean:374` | 既存 | **infinitePi → Fin n 積の主役** |
| `infinitePi` 有限 ι で `= Measure.pi` | `MeasureTheory.Measure.infinitePi_eq_pi` | `ProductMeasure.lean:509` | 既存 | `[Fintype ι]` 版 (Fin n 直接) |
| Q^n singleton = `∏ chernoffMediator` | `chernoffMediatorMeasure_pi_singleton` | `ChernoffPerTiltSanov.lean:197` | **既存(自作済)** | pmf 形接続 (`Measure.pi (Fin n)`) |
| 同 `toReal` 形 | `chernoffMediatorMeasure_pi_singleton_toReal` | `ChernoffPerTiltSanov.lean:219` | **既存(自作済)** | `∑∏ chernoffMediator` 直結 |
| Q^n は確率測度 | `chernoffMediatorMeasure_pi_isProbability` | `ChernoffPerTiltSanov.lean:235` | **既存(自作済)** | `IsFiniteMeasure` 供給 |
| 集合測度 = ∑ singleton (有限 α) | `MeasureTheory.measure_biUnion_finset` 系 / `Finset.sum` | Mathlib + 既存パターン | 既存 | band set → `∑_{x∈band}` |

`infinitePi_map_restrict` 結論形 verbatim:
```
theorem infinitePi_map_restrict {I : Finset ι} :
    (Measure.infinitePi μ).map I.restrict = Measure.pi fun i : I ↦ μ i
```
**前提事故ポイント**: 右辺は `Measure.pi (fun i : ↥I ↦ μ i)` — 添字が**部分型 `↥I`**。
band は `Measure.pi (fun _ : Fin n ↦ Q)` (= 既存 `chernoffMediatorMeasure_pi_singleton`)。
`I := Finset.range n` とすると `↥(Finset.range n) ≃ Fin n` の reindex が要る (下記自作 #4)。

### G. 境界ケース `λ*∈{0,1}` の処理素材 (既存)

| 概念 | Mathlib API / 既存補題 | file:line | 状態 | discharge での扱い |
|---|---|---|---|---|
| `Z(0) = 1` | `chernoffZSum_lam_zero` | `Chernoff.lean:76` | 既存 | 端点で `−log Z = 0` |
| `Z(1) = 1` | `chernoffZSum_lam_one` | `Chernoff.lean:90` | 既存 | 同上 |
| `chernoffInfo ≥ 0` | `chernoffInfo_nonneg` | `Chernoff.lean:183` | 既存 | 端点 min → `chernoffInfo=0` |
| mediator 端点 = P₁/P₂ | `chernoffMediator_lam_zero/one` | `Chernoff.lean:560/570` | 既存 | 端点で Q=P₁ (or P₂) |

---

## 主要前提条件ボックス

discharge で「前提事故」を起こしやすい lemma の typeclass / 仮定を逐条:

- **`strong_law_ae_real`**: typeclass 制約 **なし**。仮定は `Integrable (X 0) μ` /
  `Pairwise (· ⟂ᵢ[μ] · on X)` / `∀ i, IdentDistrib (X i) (X 0) μ μ`。有限 `α` + bounded
  `Y = log P₁ − log P₂` (full support `>0` で有界) なので `Integrable` 自明。極限は `μ[X 0]`
  であって 0 ではない — **一次最適性で `μ[X 0]=0` を別途証明してから使う**。
- **`tendstoInMeasure_of_tendsto_ae`**: **`[IsFiniteMeasure μ]` 必須**。`infinitePi Q` は
  `IsProbabilityMeasure` (自動 instance) なので OK。`AEStronglyMeasurable (f n)` は有限 `α`
  + 連続関数で自明。
- **`iIndepFun_infinitePi`**: **`[∀ i, IsProbabilityMeasure (P i)]` 必須**、`ι` は Fintype 不要。
  Q は `chernoffMediatorMeasure_isProbabilityMeasure` で確率測度 (full support `>0` が前提)。
- **`iIndepFun_pi` は使わない** (`[Fintype ι]` で `ℕ` 不可)。誤って掴むと SLLN に接続できない。
- **`infinitePi_map_restrict`**: 右辺 `Measure.pi (fun i : ↥I ↦ μ i)` の**部分型添字**。
  `Fin n` 形への reindex を別途要する (gap でなく plumbing)。
- **`IsMinOn.isLocalMin`**: `hs : s ∈ 𝓝 a` を要求 → `s = Icc 0 1`, `a = λ*` のとき
  `interior_Icc` + `λ*∈Ioo 0 1` で近傍性。**`λ*` が端点だとこの近傍性が崩れる**
  (= 境界ケースで一次条件が立たない理由)。

---

## 自作が必要な要素 (優先度順)

genuine な Mathlib gap は**ゼロ**。すべて plumbing / 接続 / 既存補題の流用。

1. **`chernoffInfo_attained_isMinOn` (補助、最優先)** — `chernoffInfo_attained` を
   `IsCompact.exists_isMinOn` で書き直し、`∃ λ*∈Icc, IsMinOn (Z) (Icc 0 1) λ* ∧
   chernoffInfo = -log Z(λ*)` を出す。**~15-30 行**。落とし穴: `Z` の min と `log∘Z` の min は
   `log` 単調で同値だが、Fermat は `Z` 側でやる方が `Z'` 計算が直接 (`log Z` だと商微分が増える)。
2. **`hasDerivAt_chernoffZSum` (一次最適性の核、~30-50 行)** — `HasDerivAt (Z)
   (∑ a, chernoffZSum·chernoffMediator a·(log P₂ a − log P₁ a)) lam`。各項
   `const_rpow×const_rpow` を `.mul`、`.sum` で集約。落とし穴: `(P₁ a)^(1-λ)` は指数が
   `1-λ` (合成) なので `HasDerivAt.const_rpow` (合成版) を使う; `(P₂ a)^λ` は
   `hasStrictDerivAt_const_rpow` → `.hasDerivAt`。符号 (`log P₂ − log P₁`) に注意
   (band は `log P₁ − log P₂`)。
3. **`chernoffMediator_mean_logRatio_eq_zero` (一次最適性の帰結、~20-40 行)** —
   #1 の `IsMinOn` + #2 の `HasDerivAt` + `IsMinOn.isLocalMin` (`interior_Icc`,
   `λ*∈Ioo`) + `IsLocalMin.hasDerivAt_eq_zero` で `∑ a, chernoffMediator·(log P₁−log P₂) = 0`。
   落とし穴: **`λ*∈Ioo 0 1` を前提に置く** (境界は #6 で別処理)。
4. **`chernoffBandMass_via_slln` (Q-LLN 本体 + reindex、~80-150 行、最大)** —
   `Y a := log(P₁ a) − log(P₂ a)`, `Q := chernoffMediatorMeasure P₁ P₂ λ*`,
   `infinitePi (fun _:ℕ => Q)` 上で:
   (i) `CramerLC2Discharge.iIndepFun_eval_under_infinitePi` /
   `identDistrib_eval_under_infinitePi` を **流用/再特化** (template 既存) →
   `iIndepFun` + `IdentDistrib`、`iIndepFun.indepFun` で `Pairwise ⟂ᵢ`;
   (ii) `strong_law_ae_real` → a.s.; (iii) `μ[Y∘eval 0] = ∑_a Q(a)·Y(a) = 0` (#3 から);
   (iv) `tendstoInMeasure_of_tendsto_ae` → band 補集合 mass → 0;
   (v) `infinitePi_map_restrict` + `chernoffMediatorMeasure_pi_singleton_toReal` で
   `Fin n`/`∑∏ chernoffMediator` 形へ橋渡し。
   **落とし穴 (最大)**: SLLN の `∑ i∈range n` (添字 `ℕ`/部分型) ↔ band の `∑ i:Fin n` の
   reindex。`Finset.range n ≃ Fin n`、`infinitePi_map_restrict` の `↥I` 添字、
   band set の `Fin n → α` 形と `ℕ → α` の射影整合。**ここが想定外膨張すれば L-SD1 退避を検討**
   (ただし下記の通り L-SD1 の「Mathlib gap」根拠は**実際には不在**なので、退避しても
   honest hyp の load-bearing 度は変わらない — plumbing 規模の問題)。
5. **`chernoffBandMass_eventually_half` (集約、~15-30 行)** — #4 の「band mass → 1」から
   `∀ε>0, ∀ᶠ n, 1/2 ≤ band mass` = `IsChernoffBandMassToOne` の定義一致。
   `Tendsto _ (𝓝 1)` + `eventually_ge_of_tendsto_gt (1/2 < 1)`。
6. **`chernoff_converse_boundary_case` (境界ケース、~30-60 行)** — `λ*∈{0,1}` のとき。
   `Z(0)=Z(1)=1` ⇒ `chernoffInfo = -log 1 = 0` (端点 min)。converse `limsup rate ≤ 0` を
   **別経路で**(`bayesErrorMinPmf ≤ 1` から `rate ≥ 0` でなく、`limsup rate ≤ 0` は
   `bayesErrorMinPmf ≥ (1/2)·min(P₁,P₂)^n` 程度の下界で出る — 既存 achievability
   `bayesErrorMinPmf_le_half_Z_pow` の逆向き素材を要確認)。**落とし穴**: 境界 min を
   完全に避けるには「内点に min が必ずある」十分条件 (例: `P₁ ≠ P₂` ⇒ `Z` 端点で
   微分符号が内向き) を別途証明する道もあるが、case-split の方が安全。

---

## 撤退ラインへの距離

親計画 [`chernoff-converse-sanov-discharge-plan.md`](chernoff-converse-sanov-discharge-plan.md)
の撤退ライン:

### L-SD1 (step 3 の Sanov LLN 移植が Mathlib gap; `Measure.pi` coordinate 独立→`IndepFun` 橋欠如)

**判定: 発動しない (gap は実在しない)**。

L-SD1 の前提だった「`Measure.pi` の coordinate 独立を `IndepFun` 形に変換する Mathlib 補題が
欠けている」は**事実誤認**:
- `iIndepFun_infinitePi` (`InfinitePi.lean:103`, **Fintype 不要**) が `ℕ`-indexed 無限積で
  coordinate iIndepFun を直接供給。
- `iIndepFun.indepFun` (`Basic.lean:447`) で `Pairwise (· ⟂ᵢ[μ] ·)` を取得。
- `identDistrib_eval_under_infinitePi` (`CramerLC2Discharge.lean:141`) が **本プロジェクトに
  既存テンプレ**として IdentDistrib を供給済み (Cramér の同型 plumbing)。

→ step 3 は honest hyp 化せず **genuine に discharge 可能**。L-SD1 を採る理由がない。

### L-SD2 (`bayesErrorMinPmf` redefine が安いと判明)

**判定: 発動しない**。本調査は `IsChernoffBandMassToOne` の**消費側**(band-mass→1 の供給)を
調べたもので、`bayesErrorMinPmf` の定義には触れない。F 節の橋
(`chernoffMediatorMeasure_pi_singleton_toReal` 既存) で pmf 形のまま接続でき、redefine 不要。
親計画の「現判断: L-SD2 は採らない」を維持。

### 新規縮退案 (本調査で判明した plumbing リスクへの保険)

自作 #4 (Q-LLN + reindex) が **150 行を大きく超え** `Fin n`↔`range n` reindex で
2 週間溶ける兆候が出たら、**step 3 のみ** honest hyp で退避する縮退案を提案
(L-SD1 とは根拠が違う: 「Mathlib gap」でなく「reindex plumbing の工数超過」):

```lean
/-- NOT a discharge. load-bearing residual: 一次最適性 (E_Q[log P₁−log P₂]=0) は
genuine に証明済みだが、SLLN の `infinitePi`/`range n` 形から band の `Fin n`/`∑∏` 形への
reindex plumbing が工数超過のとき退避。型 ≠ 結論 (結論は band mass→1、これは reindex 後の形)。 -/
def IsChernoffSllnReindexBridge (P₁ P₂ : α → ℝ) (lam : ℝ) : Prop := ...
```
ただし **#1-#3 (一次最適性) と #4 の SLLN 本体 ((i)-(iv)) は genuine 必須**、reindex (v) のみ。
name laundering 禁止 (`*_discharged` 不可)。本来は plumbing なので退避せず通すのが正道。

---

## 着手 skeleton

`Common2026/Shannon/ChernoffBandMassDischarge.lean` の出だし (imports は既存
`CramerLC2Discharge` / `CramerLC2PhaseC` の stack を踏襲):

```lean
import Common2026.Shannon.ChernoffSanovDischarge
import Common2026.Shannon.ChernoffPerTiltSanov
import Common2026.Shannon.Chernoff
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.LocalExtr

/-!
# Chernoff converse — band-mass discharge (`IsChernoffBandMassToOne`)

(a) 一次最適性 (`hasDerivAt_chernoffZSum` + Fermat) で `E_Q[log P₁−log P₂]=0`、
(b) Q-LLN (`strong_law_ae_real` on `infinitePi Q` + `tendstoInMeasure_of_tendsto_ae`)
で band mass → 1。撤退ライン L-SD1 は不発 (`iIndepFun_infinitePi` 実在)。
-/

namespace InformationTheory.Shannon.ChernoffBandMassDischarge

open Real MeasureTheory ProbabilityTheory Filter Finset
open InformationTheory.Shannon.Chernoff
open InformationTheory.Shannon.ChernoffSanovDischarge
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- (a) `Z(λ)` の `λ`-微分: `Z'(λ) = ∑_a Z·chernoffMediator a·(log P₂ a − log P₁ a)`. -/
lemma hasDerivAt_chernoffZSum
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) (lam : ℝ) :
    HasDerivAt (fun l => chernoffZSum P₁ P₂ l)
      (∑ a, (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam * (Real.log (P₂ a) - Real.log (P₁ a))) lam := by
  sorry

/-- (a) 内点一次最適性 ⇒ Q-mean of `log(P₁/P₂)` = 0. -/
lemma chernoffMediator_mean_logRatio_eq_zero
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (hlam_int : lam ∈ Set.Ioo (0:ℝ) 1)
    (hlam_min : IsMinOn (fun l => chernoffZSum P₁ P₂ l) (Set.Icc 0 1) lam) :
    (∑ a, ChernoffConverse.chernoffMediator P₁ P₂ lam a
        * (Real.log (P₁ a) - Real.log (P₂ a))) = 0 := by
  sorry

/-- (b) Q-LLN + reindex ⇒ band mass → 1 (内点 λ* で). -/
theorem isChernoffBandMassToOne_of_interior_optimal
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (hlam_int : lam ∈ Set.Ioo (0:ℝ) 1)
    (hlam_min : IsMinOn (fun l => chernoffZSum P₁ P₂ l) (Set.Icc 0 1) lam) :
    IsChernoffBandMassToOne P₁ P₂ lam := by
  sorry

end InformationTheory.Shannon.ChernoffBandMassDischarge
```

---

## まとめ

- インベントリは **`docs/shannon/chernoff-bandmass-discharge-inventory.md`** (本ファイル)。
- (a) 一次最適性: **Mathlib に揃う** (`hasStrictDerivAt_const_rpow` + Fermat + `interior_Icc`)。
  自作は集約 plumbing #1-#3 のみ。
- (b) Q-LLN: **Mathlib に揃う + 本プロジェクトに template 既存**
  (`strong_law_ae_real` + `iIndepFun_infinitePi` + `tendstoInMeasure_of_tendsto_ae`;
  `CramerLC2Discharge` の eval-under-infinitePi 補題が再利用可)。**確率収束版は a.s.→in-measure
  で代替** (専用弱法則は名前として不在だが不要)。
- **product measure 上で LLN が使えるか**: **YES**。ただし `infinitePi` (Fintype 不要) を経由し、
  `Measure.pi (Fin n)` 直接ではない。`infinitePi_map_restrict` で Fin n 形へ橋渡し (reindex plumbing)。
- **境界ケース `λ*∈{0,1}`**: 内点一次条件が崩れる ⇒ **case-split 必須** (#6)。端点では
  `Z=1` ⇒ `chernoffInfo=0` で converse を別経路。`chernoffInfo_attained` を `IsMinOn` 付きに
  書き直す際 (#1) に内点/端点を分岐。
- 撤退ライン: **L-SD1 / L-SD2 とも不発**。L-SD1 の前提「Mathlib gap」は事実誤認
  (`iIndepFun_infinitePi` 実在)。保険として reindex 工数超過時の縮退案を新規提示。
- 最大リスク: 自作 #4 の **`Fin n` ↔ `range n` reindex plumbing** (80-150 行見込み)。
- 着手 ready。
