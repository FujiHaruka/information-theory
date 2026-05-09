## Phase 4 シャノン converse のための Mathlib 在庫調査

> ムーンショット全体計画は [`docs/shannon-moonshot-plan.md`](shannon-moonshot-plan.md)。本ファイルは Phase 4-M0 の成果物 (2026-05-09)。
>
> Fano 側の同種文書は [`docs/fano-mathlib-inventory.md`](fano-mathlib-inventory.md)。

## 一行サマリ

**`klDiv` の chain rule (`klDiv_compProd_eq_add`) と `IndepFun ↔ map prod` の同値補題は完備。一方、`mutualInfo` 自体・KL の DPI / pushforward 単調性・KL × `Measure.prod` の和分解はすべて Mathlib に不在。Phase 4-α は「mutualInfo 定義 + 基本性質」までは plumbing 1〜2 日、**DPI が最大の自作項目** (50〜150 行見込み)** の構図。撤退ライン (DPI 補題が驚くほど未整備) は **軽く触れている**。完全には踏み抜いていないが、Phase 4-α-DPI で 2 週間溶けるリスクを念頭に置く。

---

## Mathlib InformationTheory ディレクトリ全体

```
.lake/packages/mathlib/Mathlib/InformationTheory/
├── KullbackLeibler/
│   ├── Basic.lean       (klDiv 定義 + 基本性質)
│   ├── ChainRule.lean   (compProd 形 chain rule)
│   └── KLFun.lean       (klFun(x) = x*log x + 1 - x)
├── Coding/
│   ├── KraftMcMillan.lean
│   └── UniquelyDecodable.lean
└── Hamming.lean
```

**結論**: Mathlib の `InformationTheory/` 名前空間に **Shannon 系の中核 (entropy / mutualInfo / channelCapacity) は完全不在**。あるのは KL divergence + 符号理論 (Kraft-McMillan, Hamming 距離) のみ。`mutualInfo` / `MutualInfo` の文字列はリポジトリ全体に **0 件** (Mathlib 全体を grep して確認済み)。一般 `fDivergence` / `FDivergence` framework も不在 (KL は f-divergence を一般化せず単独定義)。

---

## API 在庫テーブル

### A. KL chain rule (`KullbackLeibler/ChainRule.lean`)

| 補題名 | file:line | signature 要点 | Phase 4 での扱い |
|---|---|---|---|
| **`klDiv_compProd_left`** | `ChainRule.lean:182` | `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν` (`@[simp]`) | 右 kernel 共通時の分解。`mutualInfo_comm` の補助に使えるかも |
| **`klDiv_compProd_eq_add`** | `ChainRule.lean:204` | `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` | **Phase 4-α DPI と Phase 4-β bridge の主役**。両辺 ℝ≥0∞、measurability 仮定なしで成立 |
| `integrable_llr_compProd_iff` | `ChainRule.lean:115` | `(h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η) → Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ) ↔ Integrable (llr μ ν) μ ∧ Integrable (llr (μ ⊗ₘ κ) (μ ⊗ₘ η)) (μ ⊗ₘ κ)` | Real 値 chain rule の前提。`toReal` 経由で書く場合に必要 |
| `integral_llr_compProd_eq_add` | `ChainRule.lean:151` | 上の積分形 (Real chain rule) | Phase 4-β bridge で `toReal` 経路が要るときに使う |
| `rnDeriv_compProd_mul_log_eq_mul_add` | `ChainRule.lean:103` | rnDeriv の積形 chain rule | 上 2 つの内部補題。直接は使わない見込み |
| `integrable_llr_of_integrable_llr_compProd` | `ChainRule.lean:94` | `Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ) → Integrable (llr μ ν) μ` | 同上 |

**コンテキスト**: `{μ ν : Measure 𝓧} {κ η : Kernel 𝓧 𝓨}` に `[IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η]` を要求。確率測度 + Markov kernel なら問題なし。

### B. KL の `Measure.map` (pushforward) 単調性 / DPI

| 補題名 | file:line | signature | 状態 |
|---|---|---|---|
| `klDiv (μ.map e) (ν.map e) = klDiv μ ν` (`MeasurableEquiv` 形) | — | (測度同型での KL 保存) | ❌ **不在** |
| `klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν` (一般 `Measurable` 形) | — | (post-processing inequality / DPI の核) | ❌ **不在** |

**重要**: ダイレクトな DPI 補題は **皆無**。Phase 4-α の DPI は **完全に自作**することになる。chain rule (`klDiv_compProd_eq_add`) を経由すれば導出可能 (`f` を `Kernel.deterministic` で kernel 化し、composition product 形に乗せる) が plumbing 量は読めない。

**追加発見 (Phase 4-α 着手時、2026-05-09)**: KL の MeasurableEquiv 不変性 (等号形) すら Mathlib に不在。`mutualInfo_comm` と `klDiv_prod_const_left` は両方ともこれに依存するため、**最初に `klDiv_map_measurableEquiv` を自作補題として書く必要**がある。素材は揃っている:
- `Measure.rnDeriv_map` (`MeasureTheory/Function/ConditionalExpectation/RadonNikodym.lean:83`) — pushforward の Radon-Nikodym 微分
- `MeasurePreserving` 系の `MeasureTheory/MeasurePreserving.lean`
- `MeasureTheory.integral_map`, `MeasureTheory.lintegral_map` — 測度変換下の積分
- `MeasurableEquiv.measurePreserving` の auto-derive

ただし `Integrable (llr μ ν) μ` の対応や `μ ≪ ν ↔ μ.map e ≪ ν.map e` など分岐が多く、推定 **50〜100 行**。

### C. KL × `Measure.prod` (無限積)

| 補題名 | file:line | signature | 状態 |
|---|---|---|---|
| `klDiv (μ.prod ν₁) (μ.prod ν₂) = klDiv ν₁ ν₂` | — | (片側固定の積分解) | ❌ **不在** |
| `klDiv (μ₁.prod ν₁) (μ₂.prod ν₂) = klDiv μ₁ μ₂ + klDiv ν₁ ν₂` | — | (独立積の和分解) | ❌ **不在** |

**注**: Mathlib にあるのは `Kernel.compProd` 形 (`⊗ₘ`) のみで、`Measure.prod` 形では unsupported。ただし **`Measure.prod` は constant kernel 経由で `compProd` の特例**: `μ.prod ν = μ ⊗ₘ Kernel.const _ ν`。この同一視を経由すれば `klDiv_compProd_eq_add` を `Measure.prod` 形に翻訳できる見込み。

`mutualInfo` の定義で右辺に出てくる `(μ.map Xs).prod (μ.map Yo)` は `Measure.prod` 形のため、上の翻訳補題が **Phase 4-α の plumbing 第一歩**。

### D. KL の基本性質 (`KullbackLeibler/Basic.lean`)

| 補題名 | file:line | signature | Phase 4 での扱い |
|---|---|---|---|
| `klDiv` 定義 | `Basic.lean:57` | `noncomputable def klDiv (μ ν : Measure α) : ℝ≥0∞` | `mutualInfo` の本体 |
| **`klDiv_self`** | `Basic.lean:78` | `[SigmaFinite μ] → klDiv μ μ = 0` (`@[simp]`) | `mutualInfo (μ.map Xs) (μ.map Xs) = 0` 系で活用 |
| **`klDiv_eq_zero_iff`** | `Basic.lean:377` | `[IsFiniteMeasure μ] [IsFiniteMeasure ν] → klDiv μ ν = 0 ↔ μ = ν` | **`mutualInfo_eq_zero_iff_indep` の主軸**。確率測度なら有限なので前提 OK |
| `klDiv_zero_left`, `klDiv_zero_right` | `Basic.lean` 付近 | boundary cases | 補助 |
| `klDiv_smul_*` | `Basic.lean` | 測度のスカラー倍下の KL | `hMsg_uniform` の log|M| 計算で使う可能性 |
| `mul_log_le_klDiv` | `Basic.lean:360` | `ENNReal.ofReal (μ.real univ * log (μ.real univ / ν.real univ) + ν.real univ - μ.real univ) ≤ klDiv μ ν` | KL の Pinsker 風下界。Phase 4-γ で converse 系の不等式評価に使うかも |
| `mul_klFun_le_toReal_klDiv` | `Basic.lean:338` | klFun 凸性経由の下界 | 同上、補助 |

### E. `IndepFun` API (`Probability/Independence/Basic.lean`)

| 補題 | file:line | signature 要点 | Phase 4 での扱い |
|---|---|---|---|
| `IndepFun` 定義 | `Basic.lean:144` | `def IndepFun (f : Ω → β) (g : Ω → γ) (μ : Measure Ω) : Prop := Kernel.IndepFun f g (Kernel.const Unit μ) (Measure.dirac ())` | `mutualInfo_eq_zero_iff_indep` で使う |
| **`indepFun_iff_map_prod_eq_prod_map_map`** | `Basic.lean:701` | `[IsFiniteMeasure μ] → IndepFun f g μ ↔ μ.map (fun ω => (f ω, g ω)) = (μ.map f).prod (μ.map g)` | **`mutualInfo_eq_zero_iff_indep` の橋渡し**。これと `klDiv_eq_zero_iff` の合成で一発 |
| `indepFun_iff_map_prod_eq_prod_map_map'` | `Basic.lean:685` | `[SFinite μ]` 版 | 補助 |
| `IndepFun.symm` | `Basic.lean:735` | 対称性 | `mutualInfo_comm` で活用 |
| `IndepFun.comp` / `IndepFun.comp₀` | `Probability/Independence/Kernel/IndepFun.lean` | 可測関数合成での独立性保存 | DPI 系で副次的に必要かも |

→ **`mutualInfo_eq_zero_iff_indep` は揃った素材を 2〜3 行で繋ぐだけで書ける見込み**。

### F. Markov kernel (`Probability/Kernel/`)

| API | file:line | signature 要点 | Phase 4 での扱い |
|---|---|---|---|
| **`condDistrib`** | `Kernel/CondDistrib.lean:64` | `noncomputable irreducible_def condDistrib (Y : α → Ω) (X : α → β) (μ : Measure α) [IsFiniteMeasure μ] : Kernel β Ω` | Phase 3 で既出。Phase 4-β bridge と DPI で再利用 |
| **`compProd_map_condDistrib`** | `Kernel/CondDistrib.lean:82` | `(hY : AEMeasurable Y μ) → (μ.map X) ⊗ₘ condDistrib Y X μ = μ.map (fun a => (X a, Y a))` | disintegration 等式。Phase 3 でも主役、Phase 4 で `mutualInfo` の左辺を chain rule に乗せる橋渡し |
| **`Kernel.deterministic`** | `Kernel/Basic.lean:58` | `noncomputable def deterministic (f : α → β) (hf : Measurable f) : Kernel α β` (`a ↦ Measure.dirac (f a)`) | DPI を kernel 形に翻訳するときの主役 |
| `Kernel.const` | `Kernel/Basic.lean:178` | `def const (α : Type*) {β : Type*} (μβ : Measure β) : Kernel α β` | `Measure.prod` を `compProd` に翻訳する |
| `Kernel.id` | `Kernel/Basic.lean` | `Kernel.deterministic id measurable_id` | 補助 |

### G. 補助: `Measure.prod_swap` 系

| 補題 | file | signature | Phase 4 での扱い |
|---|---|---|---|
| `Measure.prod_swap` | `MeasureTheory/Constructions/Prod/Basic.lean` 付近 | `(μ.prod ν).map Prod.swap = ν.prod μ` | `mutualInfo_comm` の主軸 |

---

## 「Phase 4-α で必要な KL 補題のうち X% が Mathlib 既存」

カウント方法: 上のテーブル A〜G から「Phase 4-α で実際に使う」項目を分母、`✅ 既存` を分子。

- **分母 (Phase 4-α 必須項目)**: 8 項目
  - `klDiv` 定義 (1), `klDiv_compProd_eq_add` (1), `klDiv_eq_zero_iff` (1), `klDiv_self` (1)
  - `IndepFun` ↔ `map prod` 同値 (1), `IndepFun.symm` (1)
  - `compProd_map_condDistrib` (1), `Kernel.deterministic` (1)
- **分子 (既存)**: 8 項目
- **既存率: 100%** (素材レベル)

ただし「Phase 4-α の主役定理を**直接**書ける高レベル API」(`mutualInfo`, post-processing DPI, KL × `Measure.prod` 分解) は **0% 既存**。これらは自前で組み立てる。

> **要約**: 「**素材は完備、組み立て (mutualInfo + DPI) は自作**」。Fano Phase 3 で `condEntropy` を自作した構図と相似。Fano では `condDistrib` から離散 PMF への翻訳補題が plumbing 主体だったが、Phase 4 では **`Measure.prod` ↔ `compProd` の翻訳** + **DPI を chain rule から導出** が主体になる。

---

## 自作が必要な要素 (優先度順)

1. **`klDiv_prod_eq_klDiv` (補助補題)** — `klDiv (μ.prod ν₁) (μ.prod ν₂) = klDiv ν₁ ν₂`。`Measure.prod = · ⊗ₘ Kernel.const _ ·` 経由で `klDiv_compProd_left` から導く。10〜20 行
2. **`mutualInfo` の定義 + `mutualInfo_nonneg`** — signature 上自明 (`ℝ≥0∞` 値)。5 行
3. **`mutualInfo_comm`** — `Measure.prod_swap` + KL の swap 不変性。10〜20 行
4. **`mutualInfo_eq_zero_iff_indep`** — `indepFun_iff_map_prod_eq_prod_map_map` + `klDiv_eq_zero_iff`。5〜10 行
5. **DPI: `mutualInfo μ Xs (f ∘ Yo) ≤ mutualInfo μ Xs Yo`** — **Phase 4-α 最大の plumbing**。chain rule から導出する戦略案:
   - joint distribution `μ.map (Xs, Yo)` を `(μ.map Xs) ⊗ₘ condDistrib Yo Xs μ` で disintegrate
   - `f ∘ Yo` 側も同様に disintegrate
   - `Kernel.deterministic f` (または `Kernel.map`) で kernel 合成し、chain rule の双方を比較
   - 期待 plumbing 量: **50〜150 行** (Mathlib に DPI 直接補題が無い分、こちらに重みが寄る)
6. **stochastic kernel 版 DPI** (オプション) — Phase 4-γ で必要なら追加

---

## 撤退ライン更新

[`shannon-moonshot-plan.md`](shannon-moonshot-plan.md) の撤退ライン:

> **Phase 4-M0 で `klDiv` の DPI / monotonicity 補題が驚くほど未整備**だった場合
> → Phase 4-α の DPI を「Mathlib の不在を埋める PR ターゲット」として上流還元方向に倒す

**判定: 軽く触れている (が完全には踏み抜かない)**。

- DPI / pushforward 単調性は **完全に不在**
- ただし chain rule (`klDiv_compProd_eq_add`) と Markov kernel API (`Kernel.deterministic`, `compProd_map_condDistrib`) は揃っている
- **DPI 自作を 2 週間予算で見込む。1 週間で書けたらそのまま Phase 4-β へ、書けなかったら撤退ラインに沿って scope を縮小**

新規追加の判定基準:

- **Phase 4-α 着手 1 週間以内に「`Measure.prod ↔ compProd` 翻訳 + `mutualInfo_eq_zero_iff_indep`」が書けない**場合
  → plumbing 想定が大幅に外れているサイン。skeleton 段階に立ち戻り、定義の選び方 (例: `mutualInfo` を `compProd` 形で直接定義する) を再検討
- **DPI が 2 週間で書けない**場合
  → Phase 4-α を「mutualInfo 定義 + 基本性質 (DPI なし)」で打ち止め、DPI は将来課題。Phase 4-β / γ には到達せず Phase 4 全体を「mutualInfo 整備フェーズ」として publish

---

## Phase 4-α 着手のための skeleton

`Common2026/Shannon/MutualInfo.lean` の出だし:

```lean
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [MeasurableSpace X]
variable {Y : Type*} [MeasurableSpace Y]

/-- Mutual information via KL divergence.
`I(X; Y) := KL(P_{X,Y} ‖ P_X ⊗ P_Y)`. -/
noncomputable def mutualInfo
    (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞ :=
  klDiv (μ.map (fun ω => (Xs ω, Yo ω)))
        ((μ.map Xs).prod (μ.map Yo))

theorem mutualInfo_nonneg (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) :
    0 ≤ mutualInfo μ Xs Yo := zero_le _

theorem mutualInfo_comm
    (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    mutualInfo μ Xs Yo = mutualInfo μ Yo Xs := by
  sorry

theorem mutualInfo_eq_zero_iff_indep
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    mutualInfo μ Xs Yo = 0 ↔ IndepFun Xs Yo μ := by
  sorry

end InformationTheory.Shannon
```

`Common2026/Shannon/DPI.lean` は `MutualInfo.lean` 完成後に着手。

---

## Phase 4-M0 まとめ

- インベントリは **`docs/shannon-mathlib-inventory.md`**(このファイル)
- Phase 4-α で使う KL 補題のうち **素材は 100% 既存**、**主役定理 (mutualInfo, DPI) は 0% 既存**
- 計画書 ([`shannon-moonshot-plan.md`](shannon-moonshot-plan.md)) の `mutualInfo` 定義案はそのまま使える
- 最大リスク: **DPI 自作の plumbing 量** (50〜150 行見込み、2 週間予算)
- 撤退ラインに「軽く触れている」判定。Phase 4-α 着手 1 週間で skeleton を割れるか、2 週間で DPI を書けるかの 2 段マイルストーンで scope を再判定する
- Phase 4-α 着手 ready
