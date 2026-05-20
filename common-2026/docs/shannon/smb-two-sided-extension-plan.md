# SMB: 2-sided stationary extension `μ_ℤ` サブ計画 🌙

> 実態整合 (2026-05-20): DONE-UNCOND (別ファイル) — 2-sided 拡張は完成済だが、
> 計画した `SMBSandwich.lean` ではなく `Common2026/Probability/TwoSidedExtension.lean`
> (141 KB、real-sorry 0; line 46-52 の `sorry` 言及は古い doc コメントのみ) に実装。
> 主要 decl: `μZ` (:348)、`shiftZ` (:393) + `measurePreserving_shiftZ` (:417)、
> `ergodic_shiftZ` (:956)、`natProj` (:706) + `measurePreserving_natProj` (:727)、
> `forwardEmbed` (:505)。これらが無条件 `shannon_mcmillan_breiman`
> (`SMBAlgoetCover.lean:2840`、import :3 で TwoSidedExtension を取り込む) の
> `algoet_cover_liminf_bound` (:2751) の `liminf ≥ entropyRate` 段を支える。全 Phase M0–H 達成。
>
> **Parent**: [`shannon-mcmillan-breiman-phase-d-plan.md`](shannon-mcmillan-breiman-phase-d-plan.md) §"残: Algoet–Cover sandwich" `h_liminf` 段
>
> 親 plan の Algoet–Cover sandwich のうち **`liminf blockLogAvg ≥ entropyRate` (lower bound)** は、
> 片側 shift 上では Levy upward を「`σ(X_{-1}, X_{-2}, …)`」に適用できないため discharge 不能。
> 本サブ計画は、Mathlib + 本プロジェクトの既存 API の上に **2-sided 定常拡張**
> `μ_ℤ : Measure (ℤ → α)` を組み立て、その上で backward filtration を取って Levy
> downward (本プロジェクト `BackwardMartingale.ae_tendsto` 経路) を起動する基盤を作る。

## 進捗

- [x] M0 — Mathlib 在庫 + Route 決定 (Route A vs B) ✅
- [x] Phase A — file 構造 / namespace / imports ✅ (`Common2026/Probability/TwoSidedExtension.lean`)
- [x] Phase B — cylinder + shifted finite-marginal の定義 ✅
- [x] Phase C — projective consistency + σ-additivity ✅
- [x] Phase D — Carathéodory 拡張で `μZ : Measure (ℤ → α)` 構成 ✅ (TwoSidedExtension.lean:348)
- [x] Phase E — `shiftZ` の `MeasurePreserving` + `Ergodic` ✅ (`measurePreserving_shiftZ` :417 / `ergodic_shiftZ` :956)
- [x] Phase F — coupling (ℕ-projection 一致) ✅ (`natProj` :706 / `forwardEmbed` :505 / `measurePreserving_natProj` :727)
- [x] Phase G — past filtration + `pmfLogCondInfty` (Levy 適用) ✅
- [x] Phase H — `liminf` SMB lower bound discharge ✅ (`SMBAlgoetCover.lean:algoet_cover_liminf_bound:2751`)

## ゴール / Approach

`(Ω, T, μ)` 定常エルゴード + `X : Ω → α` (Fintype) から、`α^ℤ` 上の **両側** 確率測度
`μ_ℤ` を構成し、shift `σ : (ℤ → α) → (ℤ → α)` が `μ_ℤ`-preserving かつ ergodic、
かつ `(ℕ-restriction)_* μ_ℤ = (μ.map (fun ω i => X (T^[i] ω)))` (片側分布と一致)
となる canonical extension を作る。これにより:

1. backward σ-algebra `ℋ_k := cylinderEvents {n : ℤ | n ≤ -k}` が**真に減少する**
   filtration として ℕ 上に取れる (`Filtration ℕ` への直接マッピング)。
2. **`-log μ_ℤ(X_0 = · | ℋ_k) → -log μ_ℤ(X_0 = · | ⨅_k ℋ_k)` a.s.** が本プロジェクトの
   `BackwardMartingale.ae_tendsto` で起動可能。
3. (1)(2) + Birkhoff (既証) + (1)-(2) を coupling 経由で `(Ω, T, μ)` 側に pull back
   して `liminf ≥ entropyRate` を得る (Phase H)。

### 戦略の核 (Mathlib-driven 選択)

Mathlib の **`Probability/ProductMeasure.lean` における `infinitePi` 構成**が、本サブ計画で
やりたい "consistent finite-marginal family → 全空間上の measure" の構造を **既に
`piContent` (= `projectiveFamilyContent (isProjectiveMeasureFamily_pi μ)`) +
`piContent_tendsto_zero` + `AddContent.measure`** という形で持っている。我々の仕事は:

- (i) Product family の代わりに、**`(Ω, T, μ)` の shifted finite-dim marginals**
  `P_J : (J : Finset ℤ) → Measure (∀ j : J, α)`、`P_J := μ.map (fun ω => fun j : J => X (T^[j+N] ω))`
  (J を ℤ 上で平行移動して ℕ 上に投影し、片側分布を使う) で `IsProjectiveMeasureFamily` を取る。
- (ii) σ-additivity (`piContent_tendsto_zero` の対応物) を、α が **Fintype** ⇒ `ℤ → α`
  が compact + Hausdorff ⇒ 任意の closed cylinders が compact、という **tightness の
  自動成立**から導く。これは `infinitePi` 経路の i.i.d. 性に頼らない別証明だが、
  Mathlib の **`closedCompactCylinders` 経路** (`MeasureTheory.Constructions.ClosedCompactCylinders`)
  でほぼ枠が揃っている。
- (iii) Carathéodory 拡張は **`AddContent.measure`**
  (`Mathlib/MeasureTheory/OuterMeasure/OfAddContent.lean:165`) を直接呼ぶ。
  Mathlib 既存。

これが **Route A (Hahn-Kolmogorov on cylinder semiring)** の最短形。**Route B
(Ionescu-Tulcea backward via Bayes kernel inversion)** は α が Fintype でも
non-Markov stationary process の time-reversal kernel 構築が delicate (Phase D で
proof obligation 数倍) のため、**Route A 採用**。

### Approach 図

```
              ┌─────────────────────────────────────────────────────────┐
              │ Phase F coupling                                         │
              │ (Ω, T, μ)  ── ι := (fun ω i => X (T^[i] ω)) ──▶  ℕ → α  │
              │   (片側 stationary)                                       │
              └────────────────────────┬────────────────────────────────┘
                                       │ Phase D 拡張
                                       ▼
              ┌─────────────────────────────────────────────────────────┐
              │ μ_ℤ : Measure (ℤ → α)                                    │
              │   ・shift-stationary (Phase E)                            │
              │   ・(ℕ-proj)_* μ_ℤ = ι_* μ  (Phase F)                    │
              │   ・ergodic (Phase E.2、ℕ 側 ergodicity から transfer)    │
              └────────────────────────┬────────────────────────────────┘
                                       │ Phase G backward filtration
                                       ▼
              ┌─────────────────────────────────────────────────────────┐
              │ ℋ_k := cylinderEvents {n : ℤ | n ≤ -k}  ∈ Filtration ℕᵒᵈ │
              │ pmfLogCondInfty := -log μ_ℤ(coord 0 = · | ⨅ ℋ_k)         │
              │ (backward) Levy ─▶ pmfLogCond_k → pmfLogCondInfty a.s.   │
              └────────────────────────┬────────────────────────────────┘
                                       │ Phase H Algoet-Cover lower
                                       ▼
              h_liminf : ∀ᵐ ω ∂μ, entropyRate ≤ liminf blockLogAvg ω
```

### 撤退ライン (全体)

- **撤退 L1 (M0)**: 在庫で `closedCompactCylinders` 経路の σ-additivity 補題 (= compact
  cylinder の有限交差性) が既に Mathlib にある (`infinitePi` 経由でなく直接的に) と判明
  したら、Phase C の自前 σ-additivity を Mathlib 呼び出しに縮退、Phase B-D 合算で
  500-700 行に圧縮。逆に Mathlib 不在確認なら、Phase C 自前で +400-600 行。
- **撤退 L2 (Phase C 詰まり)**: σ-additivity の自前構築で 1 週超 → **`infinitePi` 経路
  への迂回**: `μ_ℤ := Measure.infinitePi (fun _ : ℤ => μ.map X)` を取り、結果として
  得られるのは **i.i.d. 拡張**で stationary だが coupling Phase F が `(Ω, T, μ)` の
  marginals と合わない (i.i.d. でない process では false)。この場合 SMB の lower
  bound 自体を「i.i.d. ⇒ AEP」に弱体化、stationary ergodic 一般の SMB は別 plan で
  保留。
- **撤退 L3 (Phase E ergodicity transfer 詰まり)**: ergodic transfer (Phase E.2) で
  Kolmogorov 0-1 / shift invariance plumbing が予測超 → SMB を `Ergodic σ μ_ℤ` を
  **仮説として受ける** 弱形に再変換、Phase E.2 自前は別 plan。Phase H は仮説下で完了。
- **総合撤退ライン**: Phase D 完 (= `μ_ℤ` 構成 + stationarity) で本サブ計画の主要
  価値の半分は達成。Phase F (coupling) 完 = lower bound discharge が組み立て可能、
  Phase H = SMB unconditional 完成。

### LOC 予算 内訳 (合計 1700-2400)

| Phase | 内容 | LOC |
|---|---|---|
| Phase A | file 構造 + skeleton (型 + sorry) | 100-150 |
| Phase B | cylinder + shifted marginal の定義 | 200-300 |
| Phase C | projective consistency + σ-additivity (`tendsto_zero`) | **500-800** (最大) |
| Phase D | Carathéodory 経由で `μ_ℤ` 構成 + 確率測度性 | 150-250 |
| Phase E | shift `MeasurePreserving` + ergodicity transfer | 250-400 |
| Phase F | coupling `(Ω, T, μ)` ↔ `μ_ℤ` の ℕ-projection 一致 | 150-250 |
| Phase G | backward filtration + `pmfLogCondInfty` + Levy 適用 | 250-350 |
| Phase H | `h_liminf` discharge (Algoet-Cover lower 経路) | 200-300 |
| **合計** | — | **1700-2400** |

Phase C が最大の不確実性 (Mathlib 補題在庫次第で ±300 行)。

---

## M0 — Mathlib 在庫 + Route 確定 (起草時の暫定確認)

### M0.1 既確認 (本 plan 起草時に裏取り済)

#### Cylinder σ-algebra / 集合演算

| API | location | 役割 |
|---|---|---|
| `cylinder (s : Finset ι) (S : Set (Π i : s, α i)) : Set (Π i, α i)` | `Mathlib/MeasureTheory/Constructions/Cylinders.lean:159` | 有限指標 cylinder |
| `measurableCylinders α : Set (Set (Π i, α i))` | `Mathlib/MeasureTheory/Constructions/Cylinders.lean` | 可測 cylinder 全体 |
| `MeasureTheory.isSetSemiring_measurableCylinders` | `Mathlib/MeasureTheory/Constructions/ProjectiveFamilyContent.lean:60` | `IsSetSemiring (measurableCylinders α)` |
| `MeasureTheory.isSetRing_measurableCylinders` | `Mathlib/MeasureTheory/Constructions/ProjectiveFamilyContent.lean:57` | `IsSetRing (measurableCylinders α)` |
| `MeasureTheory.isSetAlgebra_measurableCylinders` | `Mathlib/MeasureTheory/Constructions/ProjectiveFamilyContent.lean:52` | `IsSetAlgebra (measurableCylinders α)` |
| `MeasureTheory.generateFrom_measurableCylinders` | (同 file) | σ-algebra 生成等式 |
| `MeasurableSpace.cylinderEvents (Δ : Set ι) : MeasurableSpace (∀ i, α i)` | `Mathlib/MeasureTheory/Constructions/Cylinders.lean:397` | **`Δ` 座標のみ依存の σ-algebra** ← Phase G の `ℋ_k` で直接使用 |

#### Projective family + content + Carathéodory pipeline

| API | location | 役割 |
|---|---|---|
| `MeasureTheory.IsProjectiveMeasureFamily` | `Mathlib/MeasureTheory/Constructions/Projective.lean:45` | `J ⊆ I ⟹ P_I.map restrict = P_J` |
| `MeasureTheory.IsProjectiveLimit` | `Mathlib/MeasureTheory/Constructions/Projective.lean:116` | `∀ I, μ.map I.restrict = P_I` |
| `MeasureTheory.IsProjectiveLimit.unique` | `Mathlib/MeasureTheory/Constructions/Projective.lean:151` | 一意性 |
| `MeasureTheory.projectiveFamilyContent (hP : IsProjectiveMeasureFamily P) : AddContent ℝ≥0∞ (measurableCylinders α)` | `Mathlib/MeasureTheory/Constructions/ProjectiveFamilyContent.lean:117` | content as AddContent on cylinders |
| `MeasureTheory.projectiveFamilyContent_cylinder` | `Mathlib/MeasureTheory/Constructions/ProjectiveFamilyContent.lean:131` | content 値 = `P_J S` |
| `MeasureTheory.AddContent.measure (m : AddContent ℝ≥0∞ C) (hC : IsSetSemiring C) (hC_gen) (m_sigma_subadd : m.IsSigmaSubadditive) : Measure α` | `Mathlib/MeasureTheory/OuterMeasure/OfAddContent.lean:165` | **Carathéodory 拡張本体、Phase D で直接呼ぶ** |
| `MeasureTheory.AddContent.measure_eq` | `Mathlib/MeasureTheory/OuterMeasure/OfAddContent.lean:173` | 拡張が semiring 上で content と一致 |
| `MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum` | `Mathlib/MeasureTheory/Measure/AddContent.lean:683` | σ-additivity ⇒ σ-subadditivity |
| `MeasureTheory.addContent_iUnion_eq_sum_of_tendsto_zero` | `Mathlib/MeasureTheory/Measure/AddContent.lean:635` | "continuous at ∅" ⇒ σ-additive |

#### Compact cylinder infrastructure (Fintype α 経路で重要)

| API | location | 役割 |
|---|---|---|
| `MeasureTheory.closedCompactCylinders X : Set (Set (Π i, X i))` | `Mathlib/MeasureTheory/Constructions/ClosedCompactCylinders.lean:39` | 閉 + コンパクト基集合の cylinder |
| `MeasureTheory.empty_mem_closedCompactCylinders` | (同) `:43` | |
| `MeasureTheory.mem_closedCompactCylinders` | (同) `:47` | |
| `MeasureTheory.closedCompactCylinders.isCompact` | (同) `:66` | base set のコンパクト性 |
| `MeasureTheory.mem_measurableCylinders_of_mem_closedCompactCylinders` | (同) `:80` | 包含 |

#### Product measure (Mathlib 既存実装、Phase C の prior art)

| API | location | 役割 |
|---|---|---|
| `MeasureTheory.piContent (μ : ∀ i, Measure (X i)) : AddContent ℝ≥0∞ (measurableCylinders X)` | `Mathlib/Probability/ProductMeasure.lean:77` | i.i.d. の content |
| `MeasureTheory.piContent_tendsto_zero` | `Mathlib/Probability/ProductMeasure.lean:264` | **`(A n) ↘ ∅ ⟹ piContent (A n) → 0` の証明、本サブ計画 Phase C のテンプレ** |
| `Measure.infinitePi` / `Measure.infinitePiNat` | `Mathlib/Probability/ProductMeasure.lean:347, 196` | 構成済 i.i.d. 拡張 |
| `MeasureTheory.Measure.isProjectiveLimit_infinitePi` | `Mathlib/Probability/ProductMeasure.lean:363` | i.i.d. 拡張が projective limit |

#### Levy / 条件付き期待値 / Backward martingale

| API | location | 役割 |
|---|---|---|
| `MeasureTheory.Integrable.tendsto_ae_condExp` | `Mathlib/Probability/Martingale/Convergence.lean:360` | **Levy upward** (`ℕ`-indexed `ℱ`) |
| `MeasureTheory.tendsto_ae_condExp` | `Mathlib/Probability/Martingale/Convergence.lean:426` | upward (general `g`) |
| `Common2026/Shannon/BackwardFiltration.lean` | 自前 | `Filtration ℕᵒᵈ` 構造、`backwardFiltration T hT` |
| `Common2026/Shannon/BackwardMartingale.lean` | 自前 (837 行、0 sorry) | `BackwardMartingale.ae_tendsto` (Levy downward 経路) |

#### MissingMath (本サブ計画で自前必要)

- General **Kolmogorov extension theorem** for arbitrary consistent families on uncountable ℤ
  → 不要 (本計画は α : Fintype なので、`ℤ → α` がコンパクトで closedCompactCylinders 経由 OK)。
- **`MeasurePreserving (shift : (ℤ → α) → (ℤ → α)) μ_ℤ μ_ℤ`** → 自前 (Phase E)。
- **`Ergodic shift μ_ℤ`** → 自前 (Phase E.2、`Ergodic T μ` ⇒ ergodic ℕ-projection ⇒ ergodic
  ℤ-extension の transfer)。
- **2-sided extension の coupling** = ℕ-projection が `(X (T^[i] ω))_i` の law と一致
  という事実 → 自前 (Phase F、Phase D の uniqueness を経由)。

### M0.2 Route 比較と決定

| 観点 | Route A (Hahn-Kolmogorov on cylinder semiring) | Route B (Ionescu-Tulcea backward via time-reversal kernel) |
|---|---|---|
| Mathlib 既存 fit | ✅ `AddContent.measure` + `projectiveFamilyContent` で型レベル直結 | ⚠️ `Kernel.IsProjectiveLimit.trajFun` は forward ℕ 専用 (backward 用には Bayes kernel 反転自前) |
| σ-additivity の道具 | Fintype α ⇒ ℤ → α compact ⇒ tight ⇒ closedCompactCylinders 経由で自動 | non-Markov stationary の reverse kernel が exist することの自前構築 (Bayes 反転、measure-positive set の plumbing) |
| 失敗時の subtlety | "compact closed cylinder 有限交差性" の Mathlib 形を見つけるか自前で書く | reverse kernel の measurability が `pmfLogCond` (positivity 必要) の plumbing と二段に絡む |
| coupling Phase F 難度 | `IsProjectiveLimit.unique` で uniqueness 経由、proj が片側分布と一致するのを show | trajFun の uniqueness と reverse 構成の整合性を Bayes で示す |
| 見積 LOC | 1700-2400 | 2500-3500 |
| **採用** | **✅** | ❌ |

**Route A 採用理由**:
1. Fintype α + コンパクト位相での tightness が σ-additivity を自動化する古典的経路。
2. `AddContent.measure` の型レベル契約に乗るだけで Carathéodory が処理。
3. Phase F coupling が `IsProjectiveLimit.unique` 1 発で立つ。
4. Route B は **Bayes kernel inversion** が non-Markov でも well-defined だが、
   measure-zero subtlety (`a` で条件付け不能な点を分離する `condDistrib` の plumbing)
   が ~500 行追加 + Mathlib `condDistrib` の前提条件 (`StandardBorelSpace`) 不整合
   リスクが高い。

---

## Phase A — file 構造 / namespace / imports 📋

### スコープ

新規ファイル:

```
Common2026/Shannon/
  TwoSidedExtension.lean    ← Phase B〜F + G (~1100-1700 行)
  SMBLiminfDischarge.lean   ← Phase H 単独 (~200-300 行、TwoSidedExtension に depend)
```

(`Common2026.lean` に 2 行 `import` 追加。)

### Skeleton

```lean
import Common2026.Shannon.Stationary
import Common2026.Shannon.EntropyRate
import Common2026.Shannon.BackwardFiltration
import Common2026.Shannon.BackwardMartingale
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.Measure.AddContent

namespace InformationTheory.Shannon.TwoSided

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
```

### 鍵となる作業

- [ ] **(A.1)** namespace 切り出し (`InformationTheory.Shannon.TwoSided`) + imports
  最小化 (`Mathlib` 直 import 不可、必要モジュールのみ)
- [ ] **(A.2)** Phase B-F の主要 declaration を `:= by sorry` で sketch (LSP がエラーで
  ないことを確認、~100 行)
- [ ] **(A.3)** `Common2026.lean` に `import` 行 2 本追加

### Done 条件

- `lake env lean Common2026/Shannon/TwoSidedExtension.lean` が `sorry` warning のみで silent
- `Common2026.lean` import 追加で root もクリーン

### LOC 見積

100-150 行 (skeleton 込み)。

### Risk

- 既存 `Stationary.lean` / `EntropyRate.lean` の namespace `InformationTheory.Shannon`
  と衝突しないよう subnamespace `.TwoSided` を切る。

---

## Phase B — cylinder + shifted finite-marginal の定義 📋

### スコープ

```lean
namespace InformationTheory.Shannon.TwoSided

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable (p : StationaryProcess μ α)

/-- ℤ 上の各 finset `J` から、α^J の確率測度を `p` の片側 stationary marginal を
時刻シフトして構築する。

`J` が `{j₀, j₁, …, j_{k-1}}` (sort 済み) ならば `N ≥ -j₀` を取れば全要素が ≥ 0 に
平行移動でき、`obsTuple p (J.map (·+N)) : Ω → (J → α)` 経由で `μ.map` を取れる。
定常性により `N` の取り方に依らない (`marginal_independent_of_shift` で示す)。 -/
noncomputable def shiftedMarginal (J : Finset ℤ) : Measure (∀ j : J, α)

/-- shifted marginal が確率測度。 -/
instance instIsProbabilityMeasure_shiftedMarginal (J : Finset ℤ) :
    IsProbabilityMeasure (shiftedMarginal μ p J)

/-- shifted marginal の N-不依存性 (定常性、Phase B の核補題)。 -/
theorem shiftedMarginal_eq_of_shift_invariant
    (J : Finset ℤ) (N₁ N₂ : ℕ) (h₁ : ∀ j ∈ J, -j ≤ (N₁ : ℤ))
    (h₂ : ∀ j ∈ J, -j ≤ (N₂ : ℤ)) : ... := sorry

/-- shifted marginal の projective consistency: `J ⊆ I` で
`(shiftedMarginal I).map I.restrict_{J} = shiftedMarginal J`. -/
theorem shiftedMarginal_isProjectiveMeasureFamily :
    IsProjectiveMeasureFamily (shiftedMarginal μ p)

end InformationTheory.Shannon.TwoSided
```

### 鍵となる作業

- [ ] **(B.1) `obsTuple p (J : Finset ℕ) : Ω → (J → α)`** (ℕ 版、片側用) と
  measurability。Stationary.lean の `blockRV` は `Fin n → α` 形なので、それを
  `Finset → α` 形に reshape する補助。Mathlib API: `Finset.restrict`,
  `MeasurableSpace.pi`, `Measurable.pi`. ~30 行
- [ ] **(B.2) `shiftedMarginal μ p (J : Finset ℤ) : Measure (J → α)` の定義**:
  最小の `N` (= `Int.toNat (-J.min'.toNat)` または類似) で `J + N : Finset ℕ` を取り、
  `obsTuple p (J + N) |>.map (fun ω => ω ∘ shift_back)` から `μ.map`。
  Mathlib-shape-driven: 結論形は `Measure (∀ j : J, α)`、`MeasurableEquiv` 経由で
  reshape する必要があれば `MeasurableEquiv.piCongrLeft`
  (`Mathlib.MeasureTheory.MeasurableSpace.Defs` 周辺) を呼ぶ。~80-120 行
- [ ] **(B.3) `IsProbabilityMeasure` instance**: `μ.map _` の `isProbabilityMeasure_map`
  (Mathlib 既存) でほぼ free。~10 行
- [ ] **(B.4) `shiftedMarginal_eq_of_shift_invariant`** (定常性): `StationaryProcess.identDistrib_obs_zero`
  と `MeasurePreserving.iterate` を組み合わせ、`obsTuple` の law が時刻シフトで
  invariant であることを示す。joint version: `IdentDistrib (obsTuple (J+N₁)) (obsTuple (J+N₂))`
  を `T^[|N₁-N₂|]` の measure-preserving で導く。~80-120 行
- [ ] **(B.5) `shiftedMarginal_isProjectiveMeasureFamily`**: `J ⊆ I ⟹
  (shiftedMarginal I).map I.restrict_J = shiftedMarginal J`。`Measure.map_map` +
  `Finset.restrict` plumbing。~50-80 行

### Mathlib API (使用)

| API | location |
|---|---|
| `MeasureTheory.Measure.map` | `Mathlib/MeasureTheory/Measure/Map.lean` |
| `MeasureTheory.Measure.map_map` | `Mathlib/MeasureTheory/Measure/Map.lean` |
| `MeasureTheory.isProbabilityMeasure_map` | `Mathlib/MeasureTheory/Measure/Map.lean` |
| `MeasurableEquiv.piCongrLeft` | `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean` (近傍) |
| `Finset.restrict` | `Mathlib/Data/Finset/Pi.lean` 周辺 |
| `StationaryProcess.identDistrib_obs_zero` | `Common2026/Shannon/Stationary.lean:94` |
| `MeasurePreserving.iterate` | `Mathlib/Dynamics/Ergodic/MeasurePreserving.lean` |

### Done 条件

- 上記 5 declarations が `sorry`-free (proof-log: yes)

### LOC 見積

200-300 行。(B.2) shift index 算術と (B.4) joint stationarity が一番重い。

### Risk

- **(B.2)** `J : Finset ℤ` を `Finset ℕ` (shift) 経由で扱う際、`Finset.image (· + N) J`
  のような操作と `∀ j : J, α` (subtype) の reshape が `MeasurableEquiv.piCongrLeft`
  への適合で 50-100 行膨らむ可能性。**Mathlib-shape-driven**: もし `Finset.restrict`
  の結論形が "subtype の関数" ではなく "Finset.image 経由" だと整合させる
  bridge が必要。
- **(B.4) 定常性 lifting**: `IdentDistrib (obsTuple (J+N₁)) (obsTuple (J+N₂))` の joint
  形は `Measure.map_comp` + `MeasurePreserving.iterate.map_eq` で導出可能だが、
  `Finset → α` の reshape との順序が plumbing-heavy。

---

## Phase C — projective consistency + σ-additivity 📋 (本サブ計画 **最大の山場**)

### スコープ

```lean
namespace InformationTheory.Shannon.TwoSided

/-- `shiftedMarginal` から作る AddContent on measurableCylinders. -/
noncomputable def stationaryContent : AddContent ℝ≥0∞ (measurableCylinders (fun _ : ℤ => α)) :=
  projectiveFamilyContent (shiftedMarginal_isProjectiveMeasureFamily μ p)

/-- **σ-additivity (continuous at ∅)**: 反対方向の cylinder 列 `(A n) ↘ ∅`
に対し `stationaryContent (A n) → 0`. -/
theorem stationaryContent_tendsto_zero
    {A : ℕ → Set (∀ _ : ℤ, α)} (A_mem : ∀ n, A n ∈ measurableCylinders _)
    (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n => stationaryContent μ p (A n)) atTop (𝓝 0)

/-- `stationaryContent` is σ-sub-additive. -/
theorem stationaryContent_isSigmaSubadditive :
    (stationaryContent μ p).IsSigmaSubadditive
```

### 鍵となる作業

- [ ] **(C.1) `stationaryContent` 定義**: 1 行、`projectiveFamilyContent` を呼ぶだけ。
  ~5 行
- [ ] **(C.2) `stationaryContent_tendsto_zero`**: **本サブ計画最大の自前作業**。
  証明戦略:
  - **Fintype α + 離散位相**: `α` は finite ⇒ `(ℤ → α)` は **compact + Hausdorff +
    second-countable** (`Pi.instTopologicalSpace` + `compactSpace_pi`)。
  - 各 `A n = cylinder (s n) (S n)` で `S n ⊆ ∀ i : s n, α` は **closed**
    (`α` discrete topology ⇒ 任意の subset closed)、しかも **finite** ⇒ compact。
  - ⟹ `A n ∈ closedCompactCylinders (fun _ : ℤ => α)`
    (`cylinder_mem_closedCompactCylinders`)。
  - `A n` 自身も compact (compact 基集合の cylinder は compact、`Continuous.preimage_isCompact`
    で `restrict` の連続性経由 — `restrict` は projection で連続)。
  - **finite intersection property**: `⋂ A n = ∅` かつ 各 `A n` compact ⇒
    ある `N` で `⋂_{n ≤ N} A n = ∅` (`IsCompact.elim_finite_subcover` 双対形:
    `IsCompact.elim_finite_subfamily_closed` `Mathlib/Topology/CompactClosed.lean` 系)。
  - `(A n)` antitone なので `⋂_{n ≤ N} A n = A N`、⟹ `A N = ∅`、⟹
    `∀ n ≥ N, A n = ∅`、⟹ `stationaryContent (A n) = 0` eventually、
    ⟹ tendsto 0。
  - ~300-450 行 (closedCompactCylinders 経由の plumbing + Mathlib `IsCompact` 補題探し)
- [ ] **(C.3) `stationaryContent_isSigmaSubadditive`**: (C.2) + `isSigmaSubadditive_of_addContent_iUnion_eq_tsum`
  + `addContent_iUnion_eq_sum_of_tendsto_zero`。テンプレ呼び出し。~50 行
  (`piContent` の Mathlib 実装をそのまま真似る、`Mathlib/Probability/ProductMeasure.lean:340-346`)

### Mathlib API

| API | location |
|---|---|
| `MeasureTheory.projectiveFamilyContent` | `Mathlib/MeasureTheory/Constructions/ProjectiveFamilyContent.lean:117` |
| `MeasureTheory.closedCompactCylinders` | `Mathlib/MeasureTheory/Constructions/ClosedCompactCylinders.lean:39` |
| `MeasureTheory.cylinder_mem_closedCompactCylinders` | `Mathlib/MeasureTheory/Constructions/ClosedCompactCylinders.lean:74` |
| `MeasureTheory.mem_measurableCylinders_of_mem_closedCompactCylinders` | `Mathlib/MeasureTheory/Constructions/ClosedCompactCylinders.lean:80` |
| `IsCompact.elim_finite_subfamily_closed` | `Mathlib/Topology/Compactness/Compact.lean` 周辺 |
| `Pi.compactSpace` / `compactSpace_pi` | `Mathlib/Topology/Constructions.lean` 周辺 |
| `MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum` | `Mathlib/MeasureTheory/Measure/AddContent.lean:683` |
| `MeasureTheory.addContent_iUnion_eq_sum_of_tendsto_zero` | `Mathlib/MeasureTheory/Measure/AddContent.lean:635` |
| `MeasureTheory.isSetRing_measurableCylinders` | `Mathlib/MeasureTheory/Constructions/ProjectiveFamilyContent.lean:57` |

### Done 条件

- (C.1)-(C.3) が `sorry`-free。proof-log: yes (Phase C は本サブ計画 最大の山場、必須)。

### LOC 見積

**500-800 行**。(C.2) compact-cylinder finite intersection 経路の plumbing が予測困難。
**Mathlib 在庫次第で ±200 行**。

### Risk + 撤退

- **R1 (高)**: Mathlib に `closedCompactCylinders` の "有限交差性 → 空" 補題
  (= `IsCompact.elim_finite_subfamily_closed` の cylinder 特化形) が直接ないと、
  自前 plumbing 200 行。**M0 在庫調査で要確認** (起草時は `closedCompactCylinders.isCompact`
  までは確認、IsCompact 形での "Cantor-style" finite intersection 補題は M0 で再確認)。
- **R2 (中)**: Phase B (B.2) `shiftedMarginal` の reshape が `Finset.restrict` 経由で
  自然に書けないと、(C.2) の content 値計算で型一致苦戦。M0 で `Finset.restrict`
  の結論形を確認 → Phase B 定義で逆算する (CLAUDE.md "Mathlib-shape-driven Definitions" 原則)。
- **R3 (中)**: σ-additivity の自前構築が 2 週超 → **撤退 L2**: `infinitePi` 経路に
  迂回 (= 拡張は i.i.d.、coupling Phase F 不成立 ⇒ SMB lower bound を i.i.d. 限定化、
  general ergodic は別 plan)。

---

## Phase D — Carathéodory 拡張で `μ_ℤ` 構成 📋

### スコープ

```lean
namespace InformationTheory.Shannon.TwoSided

/-- 2-sided extension of `(Ω, T, μ, X)` to `Measure (ℤ → α)` via Carathéodory.

This is the canonical projective limit of the shifted finite-dimensional
marginals; uniqueness is `IsProjectiveLimit.unique`. -/
noncomputable def μZ : Measure (∀ _ : ℤ, α) :=
  (stationaryContent μ p).measure
    isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge
    (stationaryContent_isSigmaSubadditive μ p)

/-- `μZ` is a probability measure. -/
instance instIsProbabilityMeasure_μZ : IsProbabilityMeasure (μZ μ p)

/-- `μZ` is the projective limit of `shiftedMarginal`. -/
theorem isProjectiveLimit_μZ :
    IsProjectiveLimit (μZ μ p) (shiftedMarginal μ p)

/-- Cylinder value of `μZ` (Phase D の usable form). -/
theorem μZ_cylinder {I : Finset ℤ} {S : Set (∀ i : I, α)} (hS : MeasurableSet S) :
    μZ μ p (cylinder I S) = shiftedMarginal μ p I S

end InformationTheory.Shannon.TwoSided
```

### 鍵となる作業

- [ ] **(D.1) `μZ` 定義**: `AddContent.measure` を呼ぶ。`generateFrom_measurableCylinders`
  が `MeasurableSpace.pi = generateFrom (measurableCylinders α)` を与えるので、
  `mα ≤ ...` 形に変換する。~20 行
- [ ] **(D.2) `IsProbabilityMeasure` instance**: `μZ univ = stationaryContent univ = 1`
  via `μZ_cylinder + Set.univ = cylinder ∅ univ`。~20-40 行
- [ ] **(D.3) `μZ_cylinder`**: `AddContent.measure_eq` を呼ぶだけ。~15 行
- [ ] **(D.4) `isProjectiveLimit_μZ`**: 任意の `I` で `(μZ).map I.restrict = shiftedMarginal I`
  を show、`μZ_cylinder` + `Measure.ext_of_generate_finite`。~80-120 行

### Mathlib API

| API | location |
|---|---|
| `MeasureTheory.AddContent.measure` | `Mathlib/MeasureTheory/OuterMeasure/OfAddContent.lean:165` |
| `MeasureTheory.AddContent.measure_eq` | `Mathlib/MeasureTheory/OuterMeasure/OfAddContent.lean:173` |
| `MeasureTheory.generateFrom_measurableCylinders` | `Mathlib/MeasureTheory/Constructions/Cylinders.lean` |
| `MeasureTheory.IsProjectiveLimit` | `Mathlib/MeasureTheory/Constructions/Projective.lean:116` |

### Done 条件

- 上記 4 declarations sorry-free
- `μZ` を呼び出した downstream Phase E/F が型レベルで通る

### LOC 見積

150-250 行。

### Risk

- (D.4) `ext_of_generate_finite` のπ-system 仮定として `measurableCylinders` が
  IsPiSystem であることが要るが、`isPiSystem_measurableCylinders`
  (`Mathlib/MeasureTheory/Constructions/Cylinders.lean`) で free。

---

## Phase E — shift `MeasurePreserving` + `Ergodic` 移植 📋

### スコープ

```lean
namespace InformationTheory.Shannon.TwoSided

/-- The two-sided shift `σ : (ℤ → α) → (ℤ → α)`, `σ x i := x (i + 1)`. -/
def shiftZ : (∀ _ : ℤ, α) → (∀ _ : ℤ, α) := fun x i => x (i + 1)

theorem measurable_shiftZ : Measurable (@shiftZ α _)

/-- The 2-sided shift preserves `μZ`. -/
theorem measurePreserving_shiftZ : MeasurePreserving (@shiftZ α _) (μZ μ p) (μZ μ p)

/-- The 2-sided shift is invertible (the type ℤ supports negative shift). -/
def shiftZSymm : (∀ _ : ℤ, α) → (∀ _ : ℤ, α) := fun x i => x (i - 1)

theorem shiftZ_shiftZSymm : Function.LeftInverse shiftZSymm shiftZ
theorem shiftZSymm_shiftZ : Function.RightInverse shiftZSymm shiftZ

/-- Ergodicity of the shift, transferred from `Ergodic p.T μ`. -/
theorem ergodic_shiftZ {p : ErgodicProcess μ α} : Ergodic (@shiftZ α _) (μZ μ p.toStationaryProcess)

end InformationTheory.Shannon.TwoSided
```

### 鍵となる作業

- [ ] **(E.1) `shiftZ` 定義 + measurability** (`measurable_pi_iff` + `measurable_const`/`measurable_id`).
  ~20 行
- [ ] **(E.2) `measurePreserving_shiftZ`**: `IsProjectiveLimit.unique` 経由が最短。
  Show: `(μZ).map shiftZ` も `shiftedMarginal` の projective limit (= shift で indexing
  set がシフトしただけ、`shiftedMarginal_eq_of_shift_invariant` で値が同じ)、
  unique なので `(μZ).map shiftZ = μZ`。~100-150 行
- [ ] **(E.3) `shiftZSymm`** + inverse 等式: 機械的、~30 行
- [ ] **(E.4) `ergodic_shiftZ`** (`Ergodic.toStationary` 構造に乗せる):
  - 戦略 A: `Ergodic shiftZ μZ` ⟺ "shift-invariant set は μZ-trivial" ⟺
    "ℕ-projection で取った invariant set が ℕ-shift で invariant" ⟺ (Phase F coupling 後)
    "`Ω` 上で `T`-invariant set ⟺ μ-trivial" を Phase F の coupling 経由で transfer。
  - **依存性**: (E.4) は Phase F に依存するので、E.4 単独では sorry に残しておき、
    Phase F 完了後に裏取り (本 plan の Phase E.4 ⇄ F.x は cross-phase 依存)。
  - ~100-200 行
  - **代替経路**: `Ergodic.iff_aeMeasurable_inv...` (Mathlib API) 経由で直接 show、
    Kolmogorov 0-1 経由なしで可能か Phase E 着手時に loogle 再確認。

### Mathlib API

| API | location |
|---|---|
| `Function.Measurable.eval` / `measurable_pi_iff` | `Mathlib/MeasureTheory/MeasurableSpace/Basic.lean` |
| `MeasureTheory.MeasurePreserving` | `Mathlib/Dynamics/Ergodic/MeasurePreserving.lean:45` |
| `MeasureTheory.IsProjectiveLimit.unique` | `Mathlib/MeasureTheory/Constructions/Projective.lean:151` |
| `Ergodic` / `PreErgodic` | `Mathlib/Dynamics/Ergodic/Ergodic.lean:50` |

### Done 条件

- 上記 5 declarations sorry-free (Phase F 完了後に E.4 を裏取り完了)

### LOC 見積

250-400 行。

### Risk

- **R1 (中)**: (E.4) ergodicity transfer は Phase F coupling の "ℕ-projection の law 一致"
  を経由して、`(Ω, T, μ)` 側の ergodicity を ℤ 側に push する経路が必要。
  forward direction (`Ergodic T μ ⟹ Ergodic shift μZ`) は coupling 経由 OK だが、
  逆方向は不要。
- **R2 (中)**: `Ergodic shiftZ μZ` を **invariant set characterization** (`PreErgodic`)
  で示すのが多分自然、Mathlib `aeconst_set` (`Mathlib/Dynamics/Ergodic/Ergodic.lean`) 経由。

---

## Phase F — coupling `(Ω, T, μ)` ↔ `μ_ℤ` の ℕ-projection 一致 📋

### スコープ

```lean
namespace InformationTheory.Shannon.TwoSided

/-- The natural one-sided embedding `ι : Ω → (ℤ → α)` extended by stationarity:
ι ω i := X (T^[i.toNat] ω) for i ≥ 0, and (formally, since stationarity gives no
canonical "past") for i < 0 it can be left arbitrary — but the **law** under μ
matches the law of any consistent two-sided extension exactly on `(ℕ → α)`. -/

/-- The forward (one-sided) embedding `forwardEmbed : Ω → (ℕ → α)`. -/
def forwardEmbed : Ω → (∀ _ : ℕ, α) := fun ω i => p.obs i ω

theorem measurable_forwardEmbed : Measurable (forwardEmbed p)

/-- ℕ-restriction of `μZ` projected to `(ℕ → α)` agrees with `forwardEmbed μ`. -/
theorem μZ_nat_proj_eq :
    Measure.map (fun x : (∀ _ : ℤ, α) => fun i : ℕ => x (i : ℤ)) (μZ μ p)
      = Measure.map (forwardEmbed p) μ

/-- Cylinder-level coupling: for any `n` and `s : Fin n → α`,
the measure of the corresponding cylinder under `μZ` equals
`(μ.map (p.blockRV n)).real {s}`. -/
theorem μZ_block_cylinder_eq (n : ℕ) (s : Fin n → α) :
    μZ μ p { x | ∀ i : Fin n, x (i : ℤ) = s i }
      = (μ.map (p.blockRV n)).real {s}

end InformationTheory.Shannon.TwoSided
```

### 鍵となる作業

- [ ] **(F.1) `forwardEmbed` + measurability**: `obs i` の集合化、`measurable_pi_iff`。
  ~20 行
- [ ] **(F.2) `μZ_nat_proj_eq`**: `(μZ).map nat_proj` の cylinder 値が `shiftedMarginal`
  (= `forwardEmbed μ` の marginal) と一致することを示し、`Measure.ext_of_generate_finite`
  で結論。~100-150 行
- [ ] **(F.3) `μZ_block_cylinder_eq`**: (F.2) の系、`shiftedMarginal_pi` の具体形を
  `block_pmf_eq_block_RV_real` 系で書き直し。~50-100 行

### Mathlib API

| API | location |
|---|---|
| `MeasureTheory.Measure.ext_of_generate_finite` | `Mathlib/MeasureTheory/Measure/Typeclasses/Basic.lean` 周辺 |
| `MeasureTheory.isPiSystem_measurableCylinders` | `Mathlib/MeasureTheory/Constructions/Cylinders.lean` |
| `MeasureTheory.IsProjectiveLimit.measure_cylinder` | `Mathlib/MeasureTheory/Constructions/Projective.lean:124` |

### Done 条件

- 上記 3 declarations sorry-free
- (E.4) Phase E ergodicity transfer の裏取りが (F.2) 経由で完了

### LOC 見積

150-250 行。

### Risk

- (F.2) ℕ-projection と ℤ-cylinder の対応で `Finset.image (Int.ofNat) ...` 系の
  reshape が plumbing-heavy。**M0 で `Int.ofNat` injectivity 系の measurable
  bridge の在庫を確認**。

---

## Phase G — backward filtration + `pmfLogCondInfty` + Levy 適用 📋

### スコープ

```lean
namespace InformationTheory.Shannon.TwoSided

/-- Backward σ-algebra at depth `k`: the σ-algebra generated by coordinates `i ≤ -k`. -/
def pastSigma (k : ℕ) : MeasurableSpace (∀ _ : ℤ, α) :=
  MeasurableSpace.cylinderEvents {i : ℤ | i ≤ -(k : ℤ)}

/-- The past filtration as `Filtration ℕᵒᵈ`. -/
def pastFiltration : Filtration ℕᵒᵈ
    (MeasurableSpace.pi : MeasurableSpace (∀ _ : ℤ, α)) where
  seq k := pastSigma (OrderDual.ofDual k)
  mono' := by sorry -- larger k = deeper past, smaller σ-algebra in ℕᵒᵈ
  le' k := MeasurableSpace.cylinderEvents_le_pi

/-- The coordinate-0 evaluation. -/
def coord0 : (∀ _ : ℤ, α) → α := fun x => x 0

theorem measurable_coord0 : Measurable (@coord0 α _)

/-- Per-step conditional log-likelihood on the 2-sided side: `-log μZ(coord0 = a | pastSigma k)`. -/
noncomputable def pmfLogCondPast (k : ℕ) : (∀ _ : ℤ, α) → ℝ

/-- Limit log-likelihood (= conditional on the entire backward tail). -/
noncomputable def pmfLogCondInfty : (∀ _ : ℤ, α) → ℝ

/-- Integrability of `pmfLogCondPast k`. -/
theorem integrable_pmfLogCondPast (k : ℕ) : Integrable (pmfLogCondPast μ p k) (μZ μ p)

/-- Integrability of `pmfLogCondInfty`. -/
theorem integrable_pmfLogCondInfty : Integrable (pmfLogCondInfty μ p) (μZ μ p)

/-- **Backward Levy (downward) convergence**: per-step log-likelihood, conditioned
on deeper-and-deeper past, converges to `pmfLogCondInfty`.

Direct application of `BackwardMartingale.ae_tendsto` (本プロジェクト
`Common2026/Shannon/BackwardMartingale.lean`). -/
theorem pmfLogCondPast_tendsto_pmfLogCondInfty :
    ∀ᵐ x ∂(μZ μ p),
      Tendsto (fun k => pmfLogCondPast μ p k x) atTop (𝓝 (pmfLogCondInfty μ p x))

/-- Integral identity: `∫ pmfLogCondInfty d(μZ) = entropyRate μ p`. -/
theorem integral_pmfLogCondInfty_eq_entropyRate :
    ∫ x, pmfLogCondInfty μ p x ∂(μZ μ p) = entropyRate μ p

end InformationTheory.Shannon.TwoSided
```

### 鍵となる作業

- [ ] **(G.1) `pastSigma k` + 反単調性 (k 大 ⟹ σ-algebra 小)**:
  `MeasurableSpace.cylinderEvents` API。Index set `{i : ℤ | i ≤ -k}` は k 増加で減少。
  ~40 行
- [ ] **(G.2) `pastFiltration : Filtration ℕᵒᵈ`**: 既存 `BackwardFiltration.lean`
  パターン (`OrderDual` 経由) を踏襲、`mono'` で `cylinderEvents_mono` 適用。~50 行
- [ ] **(G.3) `pmfLogCondPast k x`**: condExp 経由で定義。**Mathlib-shape-driven**:
  `condDistrib` ではなく **`condExp` を Fintype α に対して各 atom で取って sum**
  (= 既存 `pmfLogCond` (`SMBChainRule.lean`) と同じ shape) を選択、Levy が直接
  起動する form にする。~80-120 行
- [ ] **(G.4) `pmfLogCondInfty`**: 同形を `⨅ k, pastSigma k` で取る。~30-50 行
- [ ] **(G.5) `integrable_pmfLogCondPast` / `integrable_pmfLogCondInfty`**: Fintype α ⇒
  `pmfLogCond` は本質的に bounded (mod measure-zero where the conditional probability is 0)、
  `Integrable` は `Mathlib` の `Integrable.of_bounded` 系で。~50-80 行
- [ ] **(G.6) `pmfLogCondPast_tendsto_pmfLogCondInfty`** ← **Phase G の核**:
  - `BackwardMartingale.ae_tendsto` (本プロジェクト `BackwardMartingale.lean:??`) の直接適用。
  - `pmfLogCondPast k` を `condExp` 形に書き直し、`backwardMartingale_eq_condExp`
    でこれが backward martingale であることを確認。
  - ~50-80 行 (既存 `BackwardMartingale` の使用例なので軽い)
- [ ] **(G.7) `integral_pmfLogCondInfty_eq_entropyRate`**: 期待値 = `H_∞` =
  `lim H_k` = `entropyRate` (`EntropyRate.lean` の `entropyRate_eq_lim_condEntropy`)。
  DCT または monotone convergence。~60-100 行

### Mathlib API

| API | location |
|---|---|
| `MeasurableSpace.cylinderEvents` | `Mathlib/MeasureTheory/Constructions/Cylinders.lean:397` |
| `MeasurableSpace.cylinderEvents_mono` | `Mathlib/MeasureTheory/Constructions/Cylinders.lean:403` |
| `MeasurableSpace.cylinderEvents_le_pi` | `Mathlib/MeasureTheory/Constructions/Cylinders.lean:406` |
| `MeasureTheory.Filtration` | `Mathlib/Probability/Process/Filtration.lean` |
| `MeasureTheory.condExp` | `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean` |
| `MeasureTheory.tendsto_ae_condExp` (forward, 参考) | `Mathlib/Probability/Martingale/Convergence.lean:426` |
| `BackwardMartingale.ae_tendsto` (本プロジェクト) | `Common2026/Shannon/BackwardMartingale.lean` |
| `Common2026.Shannon.backwardMartingale_eq_condExp` | `Common2026/Shannon/BackwardMartingale.lean` |

### Done 条件

- (G.1)-(G.7) sorry-free
- proof-log: yes (Levy downward 適用 + integral 評価)

### LOC 見積

250-350 行。

### Risk

- **R1 (中)**: (G.3) `pmfLogCondPast` を **`condExp` 形** で定義する vs **`condDistrib`
  形** の選択。`condDistrib` は `StandardBorelSpace α` を要求するが、`α : Fintype` で
  satisfy 可。それでも Fintype 特化の atom-wise condExp の方が Levy 適用直結なので
  **condExp 経路推奨**。
- **R2 (中)**: (G.6) Levy downward は本プロジェクトの自前 `BackwardMartingale.ae_tendsto`
  に依存、その signature が `pmfLogCondPast`-shape にハマるか M0 で確認 (起草時に
  `BackwardMartingale.lean:?` の signature を読み込み済み、適合見込み)。
- **R3 (高)**: (G.7) `pmfLogCondInfty` の期待値が `entropyRate` に一致することの証明、
  DCT で `lim` と `∫` の交換が必要。`pmfLogCondPast k` が `[0, log |α|]` 値の bounded ⇒
  dominated convergence 直適用 OK。**ただし `pmfLogCondPast k` の `μZ`-期待値が
  `conditionalEntropyTail μ p k` (片側) と一致することの **coupling 経由 transfer**
  が plumbing-heavy** (Phase F の `μZ_block_cylinder_eq` 経由)。

---

## Phase H — `liminf` SMB lower bound discharge 📋

### スコープ

```lean
namespace InformationTheory.Shannon.TwoSided

/-- **The SMB lower bound** (`h_liminf` for `shannon_mcmillan_breiman_of_sandwich`):

For an ergodic stationary process `p`, the per-symbol negative log-likelihood
satisfies `liminf ≥ entropyRate` a.s. -/
theorem liminf_blockLogAvg_ge_entropyRate
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, entropyRate μ p.toStationaryProcess
      ≤ Filter.liminf
          (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop

end InformationTheory.Shannon.TwoSided
```

これを既存 `ShannonMcMillanBreiman.lean:shannon_mcmillan_breiman_of_sandwich` の
`h_liminf` 引数として渡せば、(`h_limsup` を `SMBAlgoetCover.lean` 経由で取った上で)
**unconditional `shannon_mcmillan_breiman`** が立つ。

### 鍵となる作業

- [ ] **(H.1) Algoet-Cover lower bound on `μ_ℤ` side**:
  `(1/n) ∑_{i=0}^{n-1} -log μZ(coord_i = · | pastSigma 0..(N-1))(σ^i x)` →
  `∫ pmfLogCondInfty d(μZ) = entropyRate` (Birkhoff on `μ_ℤ`)、
  + likelihood ratio Markov: `-log P_n(block_n)(x) ≥ -log Markov_N(block_n)(x) - small`
  with high probability.
  Phase G の `pmfLogCondPast_tendsto_pmfLogCondInfty` + Birkhoff (既存
  `BirkhoffErgodic.birkhoff_ergodic_ae` を `μ_ℤ` 上の ergodic system に適用)
  + Fatou-style sandwich。~150-250 行
- [ ] **(H.2) `(Ω, T, μ)` 側に pull back**: Phase F の `μZ_block_cylinder_eq` で
  ℕ-projection の law が一致 ⟹ `blockLogAvg μ p n ω` と
  `blockLogAvg μZ Z-process n (ι ω)` が `ι`-pullback で a.s. 一致 ⟹
  liminf も pullback。~50-100 行

### Mathlib API

| API | location |
|---|---|
| `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` (Fatou 系) | `Mathlib/MeasureTheory/Integral/Bochner/...` |
| `Filter.liminf_le_liminf` | `Mathlib/Order/Filter/Basic.lean` 周辺 |
| `Common2026.Shannon.birkhoff_ergodic_ae` | `Common2026/Shannon/BirkhoffErgodic.lean` |

### Done 条件

- (H.1), (H.2) sorry-free
- 既存 `shannon_mcmillan_breiman_of_sandwich` の `h_liminf` 引数として渡せる shape
- proof-log: yes

### LOC 見積

200-300 行。

### Risk

- (H.1) Algoet-Cover lower direction の対称形 (`SMBAlgoetCover.lean` の `h_limsup`
  direction の対称) を書き起こす plumbing。`SMBAlgoetCover.lean` (1063 行、Phase D
  partial) の構造を参考に書く。
- (H.2) `ι : Ω → (ℕ → α)` の embedding 経由で `blockLogAvg` が一致することの確認、
  Phase F の coupling 等式を `Real.log` 内で書き換える plumbing。

---

## 全体 LOC 予算 / リスク一覧

### 全体 LOC 予算 (再掲)

| Phase | LOC | リスク |
|---|---|---|
| A | 100-150 | 低 |
| B | 200-300 | 中 (B.2 reshape) |
| C | **500-800** | **高 (σ-additivity 自前)** |
| D | 150-250 | 低 (Mathlib 呼び出し) |
| E | 250-400 | 中 (ergodicity transfer) |
| F | 150-250 | 中 |
| G | 250-350 | 中 (Levy downward + integral 評価) |
| H | 200-300 | 中 |
| **合計** | **1800-2800** | — |

(中央値 ~2200 行、最悪上振れ 2800 行。撤退ラインで縮退すれば 1400-1800 行)

### Critical Risks (再掲 + ランク)

1. **R1 (最大)**: **Phase C (σ-additivity) の自前構築**。
   Fintype α でも `closedCompactCylinders` 経由の "compact cylinders の有限交差性"
   を Mathlib 既存補題で書ききれるか不確実。
   **Mitigation**: M0 で `IsCompact.elim_finite_subfamily_closed` の特化形 +
   `Pi.compactSpace` の在庫を裏取り。撤退時は `infinitePi` 経路に弱体化 (= SMB
   lower bound を i.i.d. 限定化)。

2. **R2 (中)**: **Phase E.4 (ergodicity transfer)**。Phase F の coupling 経由で
   ergodicity を transfer する経路が Mathlib `Ergodic` API の `aeconst_set` 形に
   ハマるか。**Mitigation**: Phase F 完了後に裏取り、撤退時は `Ergodic σ μ_ℤ` を
   仮説として受け取る弱形。

3. **R3 (中)**: **Phase G.7 (`∫ pmfLogCondInfty = entropyRate`)**。DCT + coupling 経由の
   plumbing が ~100 行膨らむ可能性。**Mitigation**: 早期 (Phase G.5 直後) に積分等式
   の中間 lemma (= `∫ pmfLogCondPast k = conditionalEntropyTail k`) を独立 proof
   として書き、Phase G.6 完了後に lim 交換。

4. **R4 (低)**: **Phase B.4 (定常性 lifting joint version)**。Stationary.lean の
   `identDistrib_obs_zero` を joint Finset 版に lift する plumbing。**Mitigation**:
   Phase B 着手時に Mathlib `IdentDistrib.comp_left` + `Measure.map_pi` 系の在庫確認。

### Cross-phase 依存性

- E.4 (ergodicity transfer) ← F.2 (coupling)
- H.1 (Algoet lower) ← G.6 (Levy downward) ← BackwardMartingale (既存)
- H.2 ← F.3 (μZ cylinder 値 vs `μ.map blockRV`)

実装順序:
1. Phase A (skeleton)
2. Phase B → C → D (基盤、依存逆向きなし)
3. Phase F → E.4 (coupling から ergodicity)
4. Phase G (backward Levy)
5. Phase H (discharge)

(E.1-E.3 は Phase D の直後 / Phase F 前に着手可)

---

## Mathlib 寄与候補

本サブ計画完了後、以下を Mathlib 上流 PR 候補として整理:

- **2-sided stationary extension の存在 (Fintype 特化)**: `MeasureTheory.Stationary.IsoExtension`
  + uniqueness 補題。compact alphabet 系の Kolmogorov 補題の specialized form として
  単独で価値あり。
- **`closedCompactCylinders` 経路の σ-additivity (Phase C)**: もし Mathlib に
  `infinitePi` 経路だけが残っていて general projective family 用がない場合、本サブ計画
  Phase C の補題は Mathlib 還元候補。

これらは別 plan (`docs/probability/`) として切り出すと自然。

---

## 当面の next step

1. **M0 在庫調査詳細化** ← **次これ**: `IsCompact.elim_finite_subfamily_closed`
   の cylinder 特化形 / `Pi.compactSpace [∀ i, CompactSpace (X i)]` instance /
   `Int.ofNat` injectivity 系の measurable bridge の在庫確認。
   `mathlib-inventory` subagent に投げて structured per-lemma report を取得、
   `docs/shannon/smb-two-sided-extension-mathlib-inventory.md` に保存。
2. **Phase A skeleton** — `TwoSidedExtension.lean` を sorry-driven で書き始め。
3. **Phase B → C → D 着手判定** — Phase C 着手時に R1 リスク再評価、撤退判定。
4. **Phase F → E.4 → G → H** — Phase G 完で本サブ計画の主目的 (`liminf ≥
   entropyRate` discharge) 達成、Phase H で SMB unconditional 完成。
5. **Mathlib 寄与 PR 検討** — Phase D 完 (= `μZ` 構成、stationarity) で
   independent な Mathlib 寄与候補としても整形可。

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### 2026-05-17 — 起草 (subagent)

1. **Route A 採用**:
   - Fintype α + `closedCompactCylinders` 経路で σ-additivity が tightness 経由で立つ
     ことに賭ける Route A。
   - Route B (Ionescu-Tulcea backward via Bayes kernel inversion) は non-Markov
     stationary process の reverse kernel 構築が delicate (measure-zero conditioning
     point の分離が ~500 行追加) で却下。

2. **`AddContent.measure` 直接呼び出し戦略**:
   - Mathlib `Probability/ProductMeasure.lean` の `infinitePi` 構成が **completely
     analogous** な pipeline (`piContent → piContent_tendsto_zero → AddContent.measure`)
     なので、本サブ計画は同 pipeline の `piContent` を `stationaryContent` に
     差し替えるだけ、と認識。Phase D は 150-250 行に収まる見込み。

3. **Backward filtration を `cylinderEvents` で取る**:
   - 当初 "自前で `σ(X_{-1}, X_{-2}, …)` を `Filtration ℕᵒᵈ` に手で組む" 想定だったが、
     Mathlib `MeasurableSpace.cylinderEvents {i : ℤ | i ≤ -k}` で **直接取れる** ことを
     M0 段で確認。Phase G.1-G.2 が 100 行未満に縮退。

4. **既存 `BackwardFiltration.lean` / `BackwardMartingale.lean` の再利用**:
   - 本プロジェクトが既に backward martingale convergence (`BackwardMartingale.ae_tendsto`、
     837 行、0 sorry) を持っているので、Phase G.6 Levy downward 適用が 50-80 行で着地。
     これがなければ Phase G 全体が +500 行膨らんでいた。

5. **撤退 L2 (`infinitePi` 弱体化) の含意**:
   - Phase C で σ-additivity が詰まれば `μ_ℤ` を i.i.d. に弱体化 = SMB lower bound を
     i.i.d. (= AEP) に限定。**ただし AEP は既存 `AEP.lean` で完成済**なので、本サブ計画
     全体の価値が半減する。Phase C の R1 評価が **本サブ計画 着手 / 撤退の最重要
     ゲート**。

6. **Phase E.4 ergodicity transfer を Phase F 完了後に裏取り**:
   - E.4 単独では Phase F の coupling が無いと sorry のままになる、cross-phase 依存。
     起草時 (本 plan) の Phase 順序 (A→B→C→D→F→E.4→G→H) で実装する。

7. **`Int.ofNat` 経由の ℕ → ℤ inclusion の reshape**:
   - Phase F の `μZ_nat_proj_eq` で `(fun i : ℕ => x ((i : ℤ)))` 経由の ℕ-projection を
     扱う際、`(i : ℤ)` 経由の `MeasurableEquiv` が Mathlib にあるかは M0 で要確認。
     なければ ~30 行の自前 bridge。

8. **moonshot-seeds.md との関連**:
   - 本サブ計画は E-8' (SMB unconditional) の最後の gap である `h_liminf` を埋める
     ためのインフラ。完了で E-8' の "sandwich" 受け取り形が unconditional 形に昇格。
   - 親 plan (`shannon-mcmillan-breiman-phase-d-plan.md`) の Phase D は本サブ計画と
     並行・連携で進む (limsup direction は `SMBAlgoetCover.lean` 経路で別途進行中)。

## 参考

- 親 plan: [`shannon-mcmillan-breiman-phase-d-plan.md`](shannon-mcmillan-breiman-phase-d-plan.md)
- E-8 主 plan: [`shannon-mcmillan-breiman-plan.md`](shannon-mcmillan-breiman-plan.md)
- 既存実装:
  - `Common2026/Shannon/Stationary.lean` (Phase A)
  - `Common2026/Shannon/EntropyRate.lean` (Phase B)
  - `Common2026/Shannon/BackwardFiltration.lean` (Phase α)
  - `Common2026/Shannon/BackwardMartingale.lean` (Phase β、Levy downward)
  - `Common2026/Shannon/BirkhoffErgodic.lean` (Phase γ、自前 Birkhoff)
  - `Common2026/Shannon/SMBChainRule.lean` (Phase C.1-C.2 + D-partial)
  - `Common2026/Shannon/SMBAlgoetCover.lean` (Phase D, upper sandwich 進行中)
  - `Common2026/Shannon/ShannonMcMillanBreiman.lean` (Phase D wrapper, 仮説形)
- Mathlib 参考: `Mathlib/Probability/ProductMeasure.lean` (`infinitePi` 構成、
  Phase C テンプレ)
- Algoet–Cover (1988) "A sandwich proof of the Shannon-McMillan-Breiman theorem"
  (Annals of Probability) — lower bound direction
