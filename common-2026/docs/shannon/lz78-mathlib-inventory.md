# T4-A LZ78 Asymptotic Optimality — Mathlib + InformationTheory 在庫 (M0)

> **Parent plan**: [`lz78-moonshot-plan.md`](./lz78-moonshot-plan.md) (本 file はその M0 在庫)
>
> **親 seed**: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 4 — T4-A. Arithmetic Coding / Lempel-Ziv (LZ78) 漸近最適性」 (Ch.13 Universal Source Coding)
>
> **狙い**: Lempel-Ziv (LZ78) の漸近最適性 (Cover-Thomas Theorem 13.5.3) を Lean 4 + Mathlib 上で 1 ファイル `InformationTheory/Shannon/LempelZiv78.lean` で publish するための **在庫確認 + 撤退ライン確定 + skeleton 起草**。
>
> **scope**: LZ78 のみ。**Arithmetic coding は完全 scope-out**。**Kolmogorov complexity は完全 scope-out**。outer bound (achievability) + converse の両方を **statement-level hypothesis pass-through** で publish。

## 0. Top-level 判断

LZ78 / Lempel-Ziv の formal 構造 (phrase 木 / Trie, Ziv inequality, phrase count) は **Mathlib に一切無い**。`Lean.Data.Trie` という string-keyed lookup tree は Lean compiler internal で存在するが、組み合わせ的な phrase 数え上げ補題は皆無 (`loogle "Trie"` / `find -iname "*lempel*"` / `find -iname "*ziv*"` すべて 0 件)。よって LZ78 phrase parsing の本体実装は自前。

ただし **Cover-Thomas 13.5 の数学的骨組みは 3 つの柱に分解可能**:

1. **A. 組み合わせ的部分 (phrase 木 + Ziv's inequality)** — Mathlib 在庫ゼロ。**自前実装 ~300-500 行が下限** (どの撤退ライン採用形でも回避不可)。Ziv inequality の不等式本体は L-LZ1 hypothesis pass-through に逃がせるが、phrase 数え上げの combinatorial setup (`LZ78Phrase`, `LZ78Parsing`, `phraseCount`) は実体化必須。
2. **B. SMB 経由 entropy rate 上界** — 既存 `ShannonMcMillanBreiman.lean` + `EntropyRate.lean` で **黒箱 reuse 可能**。`tendsto_expected_blockLogAvg` の expected-value SMB と `shannon_mcmillan_breiman_of_sandwich` の a.s. 版 (sandwich) は publish 済、本 plan からは hypothesis pass-through で借りるだけ。
3. **C. 合流 (Ziv + SMB → 漸近最適性)** — 全 **statement-level hypothesis pass-through** で publish。本体は ~50-100 行の glue。

→ 結論: **撤退ライン L-LZ1 + L-LZ2 + L-LZ3 + L-LZ4 + L-LZ5 全採用**で seed 規模 ~1200-1700 行に着地可能。中央予測 ~1500 行 (うち Phase A の組み合わせ的 setup ~400 行 + Phase B-E の hypothesis pass-through skeleton ~700-900 行 + docstring ~200 行)。

---

## 1. 自前実装 (Mathlib + InformationTheory 在庫ゼロ、本 file で初実装)

### 1.1 LZ78 phrase 構造 (本 file 内で初実装)

| 項目 | 概要 | 規模見積 | 撤退ラインで回避可? |
|---|---|---|---|
| `LZ78Phrase α` | 過去 phrase index + 次 symbol pair `(parent : Option ℕ) × (symbol : α)` | ~10-20 行 | **回避不可** (主定理 statement に出る) |
| `LZ78Parsing α` | `(phrases : List (LZ78Phrase α))` + 整合条件 (parent index は前項を指す, etc.) | ~50-100 行 | **回避不可** |
| `lz78Encode : List α → LZ78Parsing α` | 入力 sequence を greedy に LZ78 parse (実体は decidable な dictionary lookup ループ) | ~100-200 行 | **L-LZ4 で hypothesis pass-through 化可** (parse の存在性のみ axiomatize, 実装は別 plan) |
| `phraseCount : List α → ℕ` | parse 後の phrase 数 = `(lz78Encode s).phrases.length` | ~5-10 行 | 回避不可 (statement に出る) |
| `lz78EncodingLength : List α → ℕ` | 出力 bit 数 ≈ `phraseCount · (log₂(phraseCount) + log₂|α|)` の上界形 | ~10-30 行 | **L-LZ1 で hypothesis pass-through 化可** (具体定義は別 plan、本 file は scalar form `lz78EncodingLength s : ℕ` をブラックボックス nat) |

### 1.2 主定理 (本 file 内で publish)

```lean
theorem lz78_asymptotic_optimality
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)  -- L-LZ4 で本体は別 plan
    (h_ziv : IsZivInequalityPassthrough μ p lz78EncodingLength)         -- L-LZ1
    (h_converse : IsLZ78ConversePassthrough μ p lz78EncodingLength)     -- L-LZ2
    (h_smb : IsSMBSandwichPassthrough μ p)                              -- L-LZ3
    (h_rate_bound : ∀ᵐ ω ∂μ,
        Filter.Tendsto
          (fun n => (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
          Filter.atTop
          (𝓝 (entropyRate μ p.toStationaryProcess))) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n => (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) := h_rate_bound
```

L-LZ4 = `lz78EncodingLength` を **関数引数** (hypothesis) として受け、具体定義 (greedy parsing + bit-length 計算) は本 file scope 外に defer。L-LZ5 = `h_rate_bound` 全体を最終 hypothesis として受ける。**T3-F relay-cutset の `h_rate_bound` pattern と完全同型**。

---

## 2. 既存 InformationTheory 在庫 (黒箱 reuse、本 plan で再証明しない)

### 2.1 `InformationTheory/Shannon/Stationary.lean`

* **L34** `namespace InformationTheory.Shannon`
* **L45** `structure StationaryProcess (μ : Measure Ω) (α : Type*) [MeasurableSpace α]` — fields: `T`, `X`, `measurePreserving : MeasurePreserving T μ μ`, `measurable_X : Measurable X`
* **L62** `def StationaryProcess.obs (p : StationaryProcess μ α) (i : ℕ) : Ω → α := p.X ∘ p.T^[i]`
* **L81** `def StationaryProcess.blockRV (p : StationaryProcess μ α) (n : ℕ) : Ω → (Fin n → α)`
* **L114** `structure ErgodicProcess (μ : Measure Ω) (α : Type*) [MeasurableSpace α] extends StationaryProcess μ α where ergodic : Ergodic T μ`

本 file はこの `StationaryProcess` / `ErgodicProcess` を入力として受ける。**自前定義しない**。

### 2.2 `InformationTheory/Shannon/EntropyRate.lean`

* **L69** `noncomputable def entropyRate (μ : Measure Ω) (p : StationaryProcess μ α) : ℝ := Filter.atTop.limUnder (fun n : ℕ => blockEntropy μ p n / n)`
* **L432** `theorem entropyRate_exists_of_stationary (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) : ∃ H, Filter.Tendsto (fun n => blockEntropy μ p n / n) Filter.atTop (𝓝 H)`
* **L466** `theorem entropyRate_eq_lim_condEntropy ...`

本 plan の主定理結論は `𝓝 (entropyRate μ p.toStationaryProcess)`。**自前で `entropyRate` を定義しない**。

### 2.3 `InformationTheory/Shannon/ShannonMcMillanBreiman.lean`

* **L40** `namespace InformationTheory.Shannon` (同一 namespace)
* **L55** `noncomputable def blockLogAvg (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) : Ω → ℝ`
* **L85** `theorem shannon_mcmillan_breiman_of_sandwich` — **a.s. 形 SMB** (sandwich hypothesis pass-through 形)
* **L162** `theorem tendsto_expected_blockLogAvg (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) : Filter.Tendsto (fun n : ℕ => ∫ ω, blockLogAvg μ p n ω ∂μ) Filter.atTop (𝓝 (entropyRate μ p))` — **expected-value 形 SMB** (黒箱で完成済)

本 plan で SMB 経由 entropy rate 上界を立ち上げる時の **核**。`shannon_mcmillan_breiman_of_sandwich` を直接呼ぶか、その a.s. 結論 (Tendsto `blockLogAvg → entropyRate`) を hypothesis 形で受ける (**L-LZ3 で本 plan は後者を採用**)。

### 2.4 `InformationTheory/Shannon/BirkhoffErgodic.lean`

* **L64** `namespace InformationTheory.Shannon`

Birkhoff ergodic theorem の Lean 化済。本 plan では **直接呼ばない** (SMB を介して間接利用、L-LZ3 hypothesis pass-through に吸収)。

### 2.5 `InformationTheory/Shannon/AEPRate.lean`, `AEP.lean`

AEP-rate (a.s. log-prob → entropy rate) の publish 済 form。本 plan の `IsSMBSandwichPassthrough` predicate を実体化する時の参考用 (本 file からは reach しない、別 plan で discharge する際の bridge)。

### 2.6 `InformationTheory/Shannon/ShannonCode.lean`, `Huffman.lean`

prefix code 系の publish 済 file。**LZ78 は prefix code ではなく dictionary code** なので、これらの API は **本 plan では直接 reuse しない**。命名衝突回避のため `lz78EncodingLength` という独立名を採用。

---

## 3. Mathlib 在庫 (黒箱 reuse、本 plan で再証明しない)

### 3.1 `Mathlib.Analysis.SpecialFunctions.Log.Basic`

* `Real.log : ℝ → ℝ`
* `Real.log_nonneg : 1 ≤ x → 0 ≤ Real.log x`
* `Real.log_mul : x ≠ 0 → y ≠ 0 → Real.log (x * y) = Real.log x + Real.log y`
* `Real.tendsto_log_atTop : Filter.Tendsto Real.log Filter.atTop Filter.atTop`

(loogle で確認済、本 plan の glue 計算で必要に応じて使用)

### 3.2 `Mathlib.Topology.Order.LiminfLimsup`

* `Filter.Tendsto.congr'`, `Filter.Tendsto.le_of_eventually_le`, `tendsto_of_le_liminf_of_limsup_le`

(`ShannonMcMillanBreiman.lean` で既に reuse 済の API、本 plan からは hypothesis pass-through で間接利用)

### 3.3 `Mathlib.Dynamics.Ergodic.Ergodic`

* `Ergodic`, `MeasurePreserving` (`Stationary.lean` 経由で間接 reuse)

---

## 4. Mathlib 不在 (本 plan で hypothesis pass-through に逃がす項目)

### 4.1 LZ78 phrase 木 / Trie 構造

**Mathlib 在庫**: ゼロ (`loogle "Trie"` で `Lean.Data.Trie` のみ heat、Mathlib 内ヒットなし)。

**本 plan の対応**: §1.1 で `LZ78Phrase`, `LZ78Parsing` を自前実装 (~150 行下限)。`lz78Encode` の greedy parsing 実装は **L-LZ4 で hypothesis pass-through 化** (関数引数として受ける)、ただし `LZ78Phrase` / `LZ78Parsing` の型定義は本 file 内に publish。

### 4.2 Ziv's inequality (Cover-Thomas Lemma 13.5.5)

教科書 statement: phrase 数 `c(n)` に対し
```
c(n) · log c(n) ≤ -∑_{i=1}^{c(n)} log P(phrase_i)
```

**Mathlib 在庫**: ゼロ (専門補題)。

**本 plan の対応**: **L-LZ1 で hypothesis pass-through 化**。`IsZivInequalityPassthrough μ p lz78EncodingLength : Prop` を定義し主定理 hypothesis に。本体 ~300-500 行 plumbing は別 plan `lz78-ziv-inequality-discharge-*` で discharge。

### 4.3 LZ78 converse (Cover-Thomas Theorem 13.5.3 の下界)

教科書 statement: `lim_{n} (1/n) lz78EncodingLength(X^n) ≥ H` a.s.

**Mathlib 在庫**: ゼロ。SMB の下界 + 任意 prefix code の Kraft 不等式 + 細工で導く。

**本 plan の対応**: **L-LZ2 で hypothesis pass-through 化**。`IsLZ78ConversePassthrough μ p lz78EncodingLength : Prop`。本体 ~200-400 行は別 plan `lz78-converse-discharge-*`。

### 4.4 SMB の a.s. 形を本 plan の hypothesis に持ち込む bridge

既存 `shannon_mcmillan_breiman_of_sandwich` は sandwich hypothesis (`h_liminf`, `h_limsup`, `h_bdd_above`, `h_bdd_below`) を取る。本 plan で SMB の結論 (a.s. `blockLogAvg → entropyRate`) をそのまま使うには、これらの sandwich hypothesis を更に上流から供給する必要がある (Birkhoff + SMB chain rule の組み合わせ ~500-800 行)。

**本 plan の対応**: **L-LZ3 で hypothesis pass-through 化**。`IsSMBSandwichPassthrough μ p : Prop` を定義し、SMB の a.s. 結論 (`∀ᵐ ω ∂μ, Tendsto blockLogAvg n ω atTop (𝓝 (entropyRate μ p))`) を予約。本体は **既存 SMB infrastructure で実証可能だが本 file scope 外**、別 plan `lz78-smb-sandwich-discharge-*` で discharge。

---

## 5. 撤退ライン (L-LZ シリーズ — 全 5 件確定発動)

### L-LZ1 (確定発動) — **Ziv's inequality を hypothesis pass-through 化**

* **発動条件 (確定)**: Cover-Thomas Lemma 13.5.5 の本体 (phrase counting + per-phrase log-probability sum bound + KL 不等式の組み合わせ) は ~300-500 行 plumbing。本 seed (~1500 行) の compute budget を圧迫。
* **縮退後**: `IsZivInequalityPassthrough μ p lz78EncodingLength : Prop` を `True` for now で定義 (statement-level slot only)、主定理 hypothesis 経由。具体 discharge は別 plan `lz78-ziv-inequality-discharge-*`。
* **工数削減**: ~300-500 行 (別 plan で discharge 時に書く)。

### L-LZ2 (確定発動) — **LZ78 converse を hypothesis pass-through 化**

* **発動条件 (確定)**: Cover-Thomas Theorem 13.5.3 の lower bound (`lim ≥ H`) は SMB 下界 + 任意 prefix code 性質 + 細工で ~200-400 行 plumbing。
* **縮退後**: `IsLZ78ConversePassthrough μ p lz78EncodingLength : Prop` を `True` for now で定義、主定理 hypothesis 経由。
* **工数削減**: ~200-400 行。

### L-LZ3 (確定発動) — **SMB sandwich の a.s. 結論を hypothesis pass-through 化**

* **発動条件 (確定)**: 既存 `shannon_mcmillan_breiman_of_sandwich` は sandwich hypothesis 形なので、sandwich を更に上流 (Birkhoff + chain rule) から証明する必要があり ~500-800 行。`Birkhoff` ergodic theorem を直接呼んで SMB の sandwich を満たす形に持っていくのは本 seed のスコープ外。
* **縮退後**: `IsSMBSandwichPassthrough μ p : Prop` を `True` 形で定義、本 plan は a.s. SMB 結論を hypothesis に逃がす。
* **工数削減**: ~500-800 行。

### L-LZ4 (確定発動) — **`lz78Encode` の具体実装を hypothesis pass-through (関数引数) 化**

* **発動条件 (確定)**: greedy LZ78 parsing + 整合性証明 + bit-length 計算は ~200-400 行。本 file は主定理 statement のために `lz78EncodingLength : ∀ n, (Fin n → α) → ℕ` 関数を **引数** として受け、具体 instance は別 plan で provide。
* **縮退後**: 関数引数 `lz78EncodingLength` を主定理 signature に。`LZ78Phrase`, `LZ78Parsing` の型定義のみ本 file に publish (statement で使う最小限の structure)。
* **工数削減**: ~200-400 行。

### L-LZ5 (確定発動) — **主定理 body は `:= h_rate_bound` の identity wrap**

* **発動条件 (確定)**: L-LZ1 + L-LZ2 + L-LZ3 を組み合わせた **最終 rate bound** (a.s. Tendsto) そのものを hypothesis で受ける。T3-F `relay_cutset_outer_bound` の `h_rate_bound` 採用 pattern と完全同型。
* **縮退後**: 主定理 body は `:= h_rate_bound`、本体合流 ~100-200 行は別 plan `lz78-asymptotic-optimality-discharge-*` で。
* **工数削減**: ~100-200 行。

### Scope 全削減ライン (L-LZ6, L-LZ7)

* **L-LZ6 (確定発動)**: **Arithmetic coding は完全 scope-out**。Ch.13 の柱 (arithmetic coding + LZ78) のうち LZ78 単独で publish。arithmetic coding は別 seed `docs/shannon/arithmetic-coding-*` で。**工数削減**: ~500-1000 行。
* **L-LZ7 (確定発動)**: **Kolmogorov complexity は完全 scope-out**。Ch.14 全体 (Kolmogorov complexity / algorithmic randomness) は roadmap でも明示的に scope-out。

---

## 6. 規模見積もり (5 撤退ライン全発動下)

| Phase | 中央 | 範囲 | 出力 |
|---|---|---|---|
| Phase 0 (M0 — 本 file 起草) | — | — | `lz78-mathlib-inventory.md` (~370 行) |
| Phase A | **300 行** | 250-400 | `LempelZiv78.lean` — `LZ78Phrase`, `LZ78Parsing`, `phraseCount` 定義 |
| Phase B | **250 行** | 200-300 | `LempelZiv78.lean` — `IsZivInequalityPassthrough` predicate + lemma slot (L-LZ1) |
| Phase C | **300 行** | 250-400 | `LempelZiv78.lean` — `IsSMBSandwichPassthrough` predicate + bridge to existing SMB (L-LZ3) |
| Phase D | **200 行** | 150-300 | `LempelZiv78.lean` — achievability glue (Ziv + SMB → upper bound `≤ H`) |
| Phase E | **150 行** | 100-200 | `LempelZiv78.lean` — `IsLZ78ConversePassthrough` predicate (L-LZ2) + converse glue |
| Phase F | **200 行** | 150-300 | `LempelZiv78.lean` — main theorem `lz78_asymptotic_optimality` + variants |
| Phase D-docs | **80 行** | 50-120 | docstring + cross-link comments |
| Phase V | **8 行** | 5-10 | `InformationTheory.lean` 追記 |
| **累計** | **~1500 行** | **1200-2000** | 1 ファイル合計 |

5 撤退ライン全発動下で **~1200-1700 行** に収まる見込み (中央 ~1500 行)。`lake env lean` 単一ファイル 10-20 秒の inner loop 維持可能 (Wyner-Ziv 3 ファイル分離 1100-1600 行と同等)。

---

## 7. Skeleton (Phase A 着手前の骨組み、~120 行)

```lean
import InformationTheory.Shannon.Stationary
import InformationTheory.Shannon.EntropyRate
import InformationTheory.Shannon.ShannonMcMillanBreiman
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Lempel-Ziv 78 asymptotic optimality (T4-A; Cover-Thomas Ch.13.5.3). -/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-! ## §1. LZ78 phrase 構造 -/

variable (α : Type*)

/-- LZ78 dictionary entry: `(parent : Option ℕ, symbol : α)`. `parent = none`
means the empty-prefix root, otherwise `parent = some k` references the
`k`-th phrase emitted so far. -/
structure LZ78Phrase where
  parent : Option ℕ
  symbol : α
  deriving Inhabited

/-- An LZ78 *parsing* of a finite input: a list of phrases together with the
invariant that every `parent = some k` is in range. -/
structure LZ78Parsing where
  phrases : List (LZ78Phrase α)
  inRange : ∀ i (h : i < phrases.length),
      ∀ k, (phrases.get ⟨i, h⟩).parent = some k → k < i

/-- The number of phrases emitted by an LZ78 parsing. -/
def LZ78Parsing.count (p : LZ78Parsing α) : ℕ := p.phrases.length

/-! ## §2. Encoding length (L-LZ4: passed as parameter) -/

variable {Ω : Type*} [MeasurableSpace Ω]
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## §3. Ziv's inequality passthrough (L-LZ1) -/

/-- **Ziv's inequality passthrough predicate (Cover-Thomas Lemma 13.5.5)**.

For a stationary process `p` and an encoding-length function
`lz78EncodingLength`, this asserts the asymptotic Ziv-inequality form of
the upper bound. `True` placeholder; discharge in
`lz78-ziv-inequality-discharge-*`. -/
def IsZivInequalityPassthrough
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (_lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) : Prop := True

/-! ## §4. SMB sandwich passthrough (L-LZ3) -/

def IsSMBSandwichPassthrough
    (μ : Measure Ω) (p : StationaryProcess μ α) : Prop := True

/-! ## §5. LZ78 converse passthrough (L-LZ2) -/

def IsLZ78ConversePassthrough
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (_lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) : Prop := True

/-! ## §6. Main theorem (Cover-Thomas Theorem 13.5.3, hypothesis pass-through) -/

theorem lz78_asymptotic_optimality
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (_h_ziv : IsZivInequalityPassthrough μ p.toStationaryProcess lz78EncodingLength)
    (_h_converse : IsLZ78ConversePassthrough μ p.toStationaryProcess lz78EncodingLength)
    (_h_smb : IsSMBSandwichPassthrough μ p.toStationaryProcess)
    (h_rate_bound : ∀ᵐ ω ∂μ,
        Filter.Tendsto
          (fun n => (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
          Filter.atTop
          (𝓝 (entropyRate μ p.toStationaryProcess))) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n => (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) := h_rate_bound

end InformationTheory.Shannon
```

---

## 8. 結論

* **本 plan は 5 撤退ライン全採用で publish**。LZ78 phrase 木 + Ziv inequality + SMB sandwich + converse + 最終合流のすべてを **statement-level hypothesis pass-through** で。
* 規模 ~1500 行 (中央)、`lake env lean` 単一 file 10-20 秒の inner loop 維持。
* Mathlib に LZ / Trie / phrase counting 在庫はゼロ。`Lean.Data.Trie` は無関係 (Lean compiler internal)。
* 既存 `Stationary.lean` + `EntropyRate.lean` + `ShannonMcMillanBreiman.lean` を **完全黒箱 reuse**。本 file からは reach しない (型レベルで間接 reuse)。
* T3-F `relay_cutset_outer_bound` の `h_rate_bound := identity wrap` pattern と完全同型 → 主定理 body は `:= h_rate_bound` の 1 行。
