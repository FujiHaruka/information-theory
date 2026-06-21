# LZ78 M3 (achievability, a.s.-eventual Ziv) — Mathlib / in-project API inventory

> 親プラン: [`docs/shannon/lz78-completion-roadmap.md`](lz78-completion-roadmap.md)（M3 = §1）。
> 攻略対象壁: `lz78GreedyImpl_achievability_ae`（`@residual(wall:lz78-aseventual-ziv)`、
> `InformationTheory/Shannon/LZ78/AsymptoticOptimality.lean:442`）。
> 本ファイルは在庫調査（実装・プラン草案はしない）。コード側タグが SoT、本ファイルは二次。

## 一行サマリ

**M3 で組み合わせる既存資産（SMB AEP / Ziv 組合せ核 / 符号長橋 / Mathlib limsup API）は
ほぼ揃っている（既存率 ~85%）。最大の構造的ギャップは 1 つ — SMB が結論する単位は nat
（`blockLogAvg → entropyRate`）だが、M3 壁の RHS は bit（`entropyRate₂`）であり、両者を繋ぐ
`/Real.log 2` 橋（`blockLogAvg₂ → entropyRate₂` の Tendsto）が「def もlemmaも存在せず、
prose のみ」。これを自前で建てる必要がある（推定 ~30–60 行、低リスク）。
本体の数学的ギャップは「`(c·log₂c)/n ≤ blockLogAvg₂ + o(n)` を a.s.-eventual / limsup 形で
SMB に乗せる」自前不等式（推定 ~150–400 行、medium）。**

具体的に self-build が要るのは 3 件:
1. **SMB-in-bits 橋** `blockLogAvg₂ → entropyRate₂`（または直接 SMB の Tendsto を `/log 2`）— ~30–60 行、低リスク。
2. **a.s.-eventual Ziv 比較不等式** `limsup (lz/n) ≤ limsup blockLogAvg₂ + o(n)`（D1/D2 の per-block 偽性を回避する length-grouping overhead 制御）— ~150–400 行、medium。
3. **`Nat.log 2`（bitLength）→ `Real.log₂`（blockLogAvg₂）の符号長単位整合** — ~20–50 行、低リスク（既存 `lz78_impl_natLog_mul_log_two_le` を再利用）。

---

## M3 壁の最終形（再掲、verbatim from `AsymptoticOptimality.lean:442`）

```lean
@[residual(wall:lz78-aseventual-ziv)]  -- docstring tag
theorem lz78GreedyImpl_achievability_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.limsup
        (fun n =>
          (lz78GreedyImplEncodingLength n
              (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
      ≤ entropyRate₂ μ p.toStationaryProcess := by
  sorry
```

`variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
[MeasurableSingletonClass α]` / `variable {Ω : Type*} [MeasurableSpace Ω]` / `open MeasureTheory ProbabilityTheory`.

証明戦略（疑似 Lean、6–10 行）:

```
-- lz78GreedyImplEncodingLength n x = c · bitLength c |α|  (c = (lz78PhraseStrings (List.ofFn x)).length)
-- Step A: 符号長 bit-rate を c·log₂c/n に: (lz/n) ≤ (c·Nat.log 2 (c+1) + c·(log₂|α|+2))/n
--          [既存: lz78_impl_rate_le_const の中身、bitLength_eq]
-- Step B: Ziv 組合せ (a.s.-eventual): limsup_n (c·log₂c/n) ≤ limsup_n blockLogAvg₂ + 0
--          [自前 M2/M3: length-grouping overhead o(n)、D1/D2 の per-block 偽性回避]
-- Step C: SMB-in-bits: ∀ᵐ ω, Tendsto blockLogAvg₂ → entropyRate₂  ⇒ limsup blockLogAvg₂ = entropyRate₂
--          [自前: shannon_mcmillan_breiman を /Real.log 2 で bit 化、Tendsto.limsup_eq]
-- Step D: filter_upwards で a.s. 合成 → limsup (lz/n) ≤ entropyRate₂
filter_upwards [smb_in_bits μ p, ziv_aseventual μ p] with ω h_smb h_ziv
calc limsup (lz/n) ≤ limsup blockLogAvg₂ := h_ziv      -- Step B
  _ = entropyRate₂ := h_smb.limsup_eq                    -- Step C (Tendsto.limsup_eq)
```

---

## A. SMB AEP 層（M3 の限界供給 — 既存・sorry-free だが単位 nat）

| 概念 | API（file:line） | 完全 signature（verbatim, [...] 含む） | 結論形（逐語） | 単位 | M3 での扱い |
|---|---|---|---|---|---|
| SMB 定理（無条件・headline） | `shannon_mcmillan_breiman`<br>`SMB/AlgoetCover/Liminf.lean:484` | `(μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α)` ＋ section vars `[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`（`omit [DecidableEq α]` 済）/ `[MeasurableSpace Ω]` | `∀ᵐ ω ∂μ, Filter.Tendsto (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess))` | **nat**（`entropyRate`, `blockLogAvg`） | **M3 の中核限界供給**。ただし結論が nat 単位なので `/Real.log 2` して bit 化が必須（Step C） |
| liminf 半分（Z→Ω 転送済） | `algoet_cover_liminf_bound`<br>`SMB/AlgoetCover/Liminf.lean:384` | `(μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α)` | `∀ᵐ ω ∂μ, entropyRate μ p.toStationaryProcess ≤ Filter.liminf (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop` | nat | 補助（M3 は Tendsto を直接使うので不要だが参考） |
| Birkhoff 経由 negLogQ tendsto | `birkhoffAverage_pmfLogCondInfty_tendsto`<br>`SMB/AlgoetCover/Liminf.lean:134` | `(μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α)` | `∀ᵐ x ∂(μZ …), Filter.Tendsto (fun n : ℕ => negLogQInftyZ … n x / (n : ℝ)) Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess))` | nat | SMB 内部足場（M3 が直接持つ必要なし） |

**単位地雷（最重要）**: `shannon_mcmillan_breiman` の結論は **`entropyRate`（nat）であって `entropyRate₂`
（bit）ではない**（`Liminf.lean:488` verbatim 確認）。M3 壁 RHS は `entropyRate₂`。両辺を `Real.log 2`
で割れば `blockLogAvg₂ → entropyRate₂` になる（`Tendsto.div_const` で機械的）が、この橋は
**存在しない**（§E 参照）。

---

## B. 符号長 / per-symbol rate 層（既存・sorry-free）

| 概念 | API（file:line） | 完全 signature（verbatim） | 結論形 | 単位 | M3 での扱い |
|---|---|---|---|---|---|
| 符号長 def | `lz78GreedyImplEncodingLength`<br>`AsymptoticOptimality.lean:78` | `(n : ℕ) (x : Fin n → α) : ℕ`、section vars `{α : Type*} [Fintype α] [DecidableEq α]` | `let c := (lz78PhraseStrings (List.ofFn x)).length; c * LZ78Phrase.bitLength c (Fintype.card α)` | **bit**（`bitLength = Nat.log 2 …`） | Step A の被分子 |
| 定数 rate 上界 | `lz78_impl_rate_le_const`<br>`AsymptoticOptimality.lean:168` | `[Nonempty α] (n : ℕ) (x : Fin n → α)` | `(lz78GreedyImplEncodingLength n x : ℝ) / (n : ℝ) ≤ (1 + 8 * Real.log (Fintype.card α + 1) / Real.log 2) + ((Nat.log 2 (Fintype.card α) : ℝ) + 2)` | bit | headline の `h_bdd_above` 内製に使用済。M3 では limsup 有界性（cobounded）に再利用可 |
| per-symbol 上界 | `lz78_impl_encoding_length_per_symbol_le`<br>`AsymptoticOptimality.lean:125` | `(n : ℕ) (hn : 0 < n) (x : Fin n → α)` | `(lz78GreedyImplEncodingLength n x : ℝ) / (n : ℝ) ≤ (Nat.log 2 (n + 1) : ℝ) + (Nat.log 2 (Fintype.card α) : ℝ) + 2` | bit | 参考 |
| per-symbol 非負 | `lz78_impl_encoding_length_per_symbol_nonneg`<br>`AsymptoticOptimality.lean:144` | `(n : ℕ) (x : Fin n → α)` | `(0 : ℝ) ≤ (lz78GreedyImplEncodingLength n x : ℝ) / (n : ℝ)` | — | limsup 下界・cobounded |
| `Nat.log 2 → Real.log` 橋 | `lz78_impl_natLog_mul_log_two_le`<br>`AsymptoticOptimality.lean:152` | `(m : ℕ)` | `(Nat.log 2 m : ℝ) * Real.log 2 ≤ Real.log m` | nat↔bit 変換 | **Step A/C の単位整合の核**。`Nat.log 2 (c+1)` を `Real.log (c+1)/Real.log 2` に降ろす |

---

## C. Ziv 組合せ核（既存・sorry-free、`c·log c ≤ K·n`）

| 概念 | API（file:line） | 完全 signature（verbatim） | 結論形 | 単位 | M3 での扱い |
|---|---|---|---|---|---|
| **Ziv 積上界** | `lz78PhraseStrings_mul_log_le`<br>`ZivCountingBody.lean:357` | `[Nonempty α] (input : List α)`、section vars `{α : Type*} [Fintype α] [DecidableEq α]` | `((lz78PhraseStrings input).length : ℝ) * Real.log ((lz78PhraseStrings input).length : ℝ) ≤ 8 * Real.log (Fintype.card α + 1) * (input.length : ℝ)` | **nat**（`Real.log`） | **M3 の組合せ核**。`c·log c ≤ 8·log(|α|+1)·n`。**K = `8 * Real.log(card α + 1)`**（コード実測、docstring の `4·log(b+1)` は誤記 — コードは 8） |
| 同・length-family 版 | `lz78PhraseStrings_mul_log_le_of_length`<br>`ZivCountingBody.lean:393` | `(input : ℕ → List α) (hlen : ∀ n, (input n).length = n) (n : ℕ)`、`[Nonempty α]` | `((lz78PhraseStrings (input n)).length : ℝ) * Real.log (…) ≤ 8 * Real.log (Fintype.card α + 1) * (n : ℝ)` | nat | `blockRV n ω` を `input n` として食わせる適用版 |
| `c = O(n/log n)` | `lz78PhraseStrings_count_isBigO`<br>`ZivCountingBody.lean:410` | `(input : ℕ → List α) (hlen : ∀ n, (input n).length = n)`、`[Nonempty α]` | `(fun n => ((lz78PhraseStrings (input n)).length : ℝ)) =O[atTop] (fun n => (n : ℝ) / Real.log (n : ℝ))` | — | overhead `(c·log log n)/n → 0` の envelope に使う |
| 距離phrase数 `c ≤ n` | `lz78PhraseStrings_count_le`<br>`GreedyLongestPrefix.lean:261` | `(input : List α)`、`{α : Type*} [DecidableEq α]` | `(lz78PhraseStrings input).length ≤ input.length` | — | `c ≤ n` |
| nodup 不変 | `lz78PhraseStrings_nodup`<br>`GreedyLongestPrefix.lean:123` | `(input : List α)`、`[DecidableEq α]` | `(lz78PhraseStrings input).Nodup` | — | 組合せ核の前提（既に内部で使用済） |
| パッキング核 | `total_length_ge_count_mul_log`<br>`ZivCountingBody.lean:190` | `(ws : List (List α)) (hnodup : ws.Nodup) (hne : ∀ w ∈ ws, w ≠ [])`、`[Fintype α] [Nonempty α]` | `(ws.length : ℝ) * Real.log (ws.length : ℝ) ≤ 8 * Real.log (Fintype.card α + 1) * ((ws.map List.length).sum : ℝ)` | nat | `lz78PhraseStrings_mul_log_le` の数学的中身。length-grouping overhead を建てる際の template |

**注**: 組合せ核は `Real.log`（nat 単位）で `c·log c ≤ K·n`。M3 Step B では bit 版
`c·log₂ c = c·log c / log 2` に落として `blockLogAvg₂ = -log₂Pₙ/n` と比較する。`/log 2` は両辺定数なので
`lz78_impl_natLog_mul_log_two_le` または単純な `div_le_div_of_nonneg_right` で機械的。

---

## D. blockLogAvg / entropyRate / 単位 def 層

| 概念 | API（file:line） | 完全 signature / def（verbatim） | 単位 | M3 での扱い |
|---|---|---|---|---|
| `blockLogAvg` def | `blockLogAvg`<br>`SMB/McMillanBreiman.lean:61` | `(μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) : Ω → ℝ := fun ω => -(1 / (n : ℝ)) * Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω})` | **nat** | SMB の対象。`n·blockLogAvg = -log Pₙ`（§下） |
| `blockLogAvg = -log Pₙ` | `blockLogAvg_eq_neg_log_blockProb`<br>`ZivEntropyBridge.lean:126` | `(μ : Measure Ω) (p : StationaryProcess μ α) {n : ℕ} (hn : 0 < n) (ω : Ω)` | `(n : ℝ) * blockLogAvg μ p n ω = - Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω})`。結論形逐語 | nat | `n·blockLogAvg = -log Pₙ` の橋。Ziv 不等式の RHS `-log Pₙ` を `n·blockLogAvg` に書換える |
| `entropyRate` def | `entropyRate`<br>`EntropyRate.lean:67` | `(μ : Measure Ω) (p : StationaryProcess μ α) : ℝ := Filter.atTop.limUnder (fun n : ℕ => blockEntropy μ p n / n)` | **nat** | SMB / M3 の nat 単位極限 |
| **`entropyRate₂` def** | `entropyRate₂`<br>`EntropyRate.lean:76` | `(μ : Measure Ω) (p : StationaryProcess μ α) : ℝ := entropyRate μ p / Real.log 2` | **bit** | **M3 壁 RHS そのもの**。`entropyRate₂ = entropyRate / Real.log 2`（実 def、sorry-free） |
| `log 2 > 0` | `log_two_pos`<br>`ZivEntropyBridge.lean:266` | （vars なし、`omit` 全） | `(0 : ℝ) < Real.log 2` | — | `/log 2` 系の正値性 |

**`entropyRate₂ = entropyRate / Real.log 2` は実 def（`EntropyRate.lean:76` verbatim 確認、sorry-free）。**
これは「単位換算」であって新規内容ではない。

**`blockLogAvg₂` は不在**（`def` も `lemma` も無し）。`ZivEntropyBridge.lean:245–261` の docstring は
「`blockLogAvg₂` / `entropyRate₂` を導入する」「`blockLogAvg₂ = blockLogAvg / log 2` は SMB から直接
`entropyRate₂` に収束する」と書いているが、**コードには `entropyRate₂` の def しか無く、`blockLogAvg₂`
の def も「SMB-in-bits」の Tendsto lemma も存在しない**（§E、§F の wall 確認）。これは docstring と
実装の乖離（prose が未実装の内容を既存であるかのように書いている）。

---

## E. Mathlib limsup / Tendsto 合成 API（既存）

| 概念 | API（file:line, Mathlib） | 完全 signature（verbatim, [...] 含む） | 結論形 | M3 での扱い |
|---|---|---|---|---|
| Tendsto → limsup 値 | `Filter.Tendsto.limsup_eq`<br>`Mathlib/Topology/Order/LiminfLimsup.lean:191` | `{f : Filter β} {u : β → α} {a : α} [NeBot f] (h : Tendsto u f (𝓝 a)) : limsup u f = a`（`α` は `[ConditionallyCompleteLinearOrder α]` 等 file 先頭 section vars） | `limsup u f = a` | **Step C の核**。SMB-in-bits の Tendsto から `limsup blockLogAvg₂ = entropyRate₂` |
| Tendsto → liminf 値 | `Filter.Tendsto.liminf_eq`<br>`Mathlib/Topology/Order/LiminfLimsup.lean:196` | `{f : Filter β} {u : β → α} {a : α} [NeBot f] (h : Tendsto u f (𝓝 a)) : liminf u f = a` | `liminf u f = a` | 参考（converse M4 側） |
| limsup 単調 | `Filter.limsup_le_limsup`<br>`Mathlib/Order/LiminfLimsup.lean:198` | `{α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β} (h : u ≤ᶠ[f] v) (hu : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault) (hv : f.IsBoundedUnder (· ≤ ·) v := by isBoundedDefault) : limsup u f ≤ limsup v f` | `limsup u f ≤ limsup v f` | **Step B**。`(lz/n) ≤ᶠ blockLogAvg₂ + err` を a.s.-eventual で建てて limsup を比較 |
| limsup ≤ 定数 | `Filter.limsup_le_of_le`<br>`Mathlib/Order/LiminfLimsup.lean:140` | `{f : Filter β} {u : β → α} {a} (hf : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault) (h : ∀ᶠ n in f, u n ≤ a) : limsup u f ≤ a` | `limsup u f ≤ a` | 別ルート（直接 `≤ entropyRate₂` の定数に乗せる場合） |
| limsup 単調（subterm 別名） | `Filter.limsup_le_limsup_of_le`<br>`Mathlib/Order/LiminfLimsup.lean`（loogle Found 1） | （未 Read、`limsup_le_limsup` と同系） | `limsup u f ≤ limsup v f` | バックアップ |
| Tendsto を定数で割る | `Filter.Tendsto.div_const`<br>`Mathlib/Topology/Algebra/GroupWithZero.lean:55` | `{x : G₀} (hf : Tendsto f l (𝓝 x)) (y : G₀) : Tendsto (fun a => f a / y) l (𝓝 (x / y))`（`G₀` は `[GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousMul G₀]` 系 section vars） | `Tendsto (fun a => f a / y) l (𝓝 (x / y))` | **SMB-in-bits 橋の機械部**。`Tendsto blockLogAvg → entropyRate` を `/Real.log 2` で `Tendsto blockLogAvg₂ → entropyRate₂` |

**`limsup_le_limsup` / `liminf_le_liminf` の cobounded/bounded 前提**: `IsCoboundedUnder (·≤·)` /
`IsBoundedUnder (·≤·)` は `:= by isBoundedDefault` のオート tactic 引数。`lz/n` は
`lz78_impl_rate_le_const`（上界）・`per_symbol_nonneg`（下界）で deterministic に有界なので、
`Filter.isBoundedUnder_of` で供給できる（既に headline `h_bdd_above`/`h_bdd_below` で実証済の手法）。
`Filter.Tendsto.limsup_eq` の `[NeBot atTop]` は ℕ の atTop なので自動成立。

---

## 重要な前提条件ボックス（事故が起きやすい lemma の前提）

- **`shannon_mcmillan_breiman`**:
  - `[IsProbabilityMeasure μ]`、`p : ErgodicProcess μ α`（**Stationary では不可、Ergodic 必須**）。
  - section vars: `[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`（`omit [DecidableEq α]` 済なので呼び出しに `DecidableEq α` は不要だが他4つは必要）。
  - **結論は `entropyRate`（nat）。`entropyRate₂` ではない** — bit 化の `/log 2` を忘れると単位 mismatch（過去 commit `99acb58` の defect 再来リスク）。
- **`Filter.Tendsto.limsup_eq`**: `[NeBot f]` 必須（ℕ atTop は OK）。`[ConditionallyCompleteLinearOrder α]` + `[TopologicalSpace]` + `[OrderTopology]` 系（ℝ は満たす）。
- **`Filter.limsup_le_limsup`**: cobounded（下）＋ bounded（上）の auto 引数 2 つ。**`lz/n` の有界性 witness を明示供給しないと `isBoundedDefault` が失敗**しうる（`lz78_impl_rate_le_const` から構成）。
- **`lz78PhraseStrings_mul_log_le`**: `[Nonempty α]` 必須。結論の K は **`8 * Real.log(card α + 1)`**（コード実測、docstring の 4 は誤記）。`Real.log`（nat 単位）。
- **`blockLogAvg_eq_neg_log_blockProb`**: `0 < n` 必須（`n = 0` で `1/0 = 0` 退化）。`0 < Pₙ`（a.s. regularity）は別途必要（observed cylinder が正質量）— Ziv 不等式を `-log Pₙ` 経由で繋ぐとき各 ω で `Pₙ > 0` が要る。

---

## 自前で建てる必要がある要素（優先度順）

### 1. **SMB-in-bits 橋** `shannon_mcmillan_breiman₂`（推奨実装 / ~30–60 行 / 低リスク）

- 内容: `∀ᵐ ω ∂μ, Tendsto (fun n => blockLogAvg₂ μ p.toStationaryProcess n ω) atTop (𝓝 (entropyRate₂ μ p.toStationaryProcess))`。
- 推奨: まず `blockLogAvg₂ μ p n := fun ω => blockLogAvg μ p n ω / Real.log 2`（または直接 inline）。`shannon_mcmillan_breiman` の Tendsto を `Filter.Tendsto.div_const · (Real.log 2)` で割り、`entropyRate / Real.log 2 = entropyRate₂`（def unfold）で書換える。
- 落とし穴: `blockLogAvg₂` を新規 def するなら `EntropyRate.lean` または `McMillanBreiman.lean` に置き、`@[entry_point]` 付与。**docstring の「既存」記述に騙されて探し回らない**（不在確定、§F）。`Tendsto.div_const` の `G₀` typeclass は ℝ で自動充足。

### 2. **a.s.-eventual Ziv 比較不等式**（~150–400 行 / medium — M3 の crux）

- 内容: `∀ᵐ ω ∂μ, limsup (fun n => lz/n) atTop ≤ limsup (fun n => blockLogAvg₂ μ p n ω) atTop`、または直接 `≤ entropyRate₂`。
- 推奨: Step A で `lz/n ≤ (c·log₂c + c·(log₂|α|+2))/n` に展開（`bitLength_eq` + `lz78_impl_natLog_mul_log_two_le`）→ `c·log₂c/n` を `blockLogAvg₂ = -log₂Pₙ/n` と比較。**length-grouping overhead `c·log(maxlen)/n`（D3、`maxlen ≤ log_b n`、`(c·log log n)/n → 0` via `count_isBigO`）で o(n) を制御**。
- 落とし穴: **per-block 形（∀n∀ω）にしてはいけない**（D1/D2 で FALSE、反例 `a^16`）。必ず limsup / a.s.-eventual。`-log Pₙ` を直接 RHS に置く（D4 の `condPhraseProb`/`blockProb_neg_log_ge_sum` path-prefix route は素通り、§F wall D4）。`lz78PhraseStrings_mul_log_le` の `Real.log`（nat）を `/log 2` で bit 化する単位整合を忘れない。

### 3. **bitLength → blockLogAvg₂ 単位整合補題**（~20–50 行 / 低リスク）

- 内容: `lz78GreedyImplEncodingLength n x / n ≤ (c·Real.log₂ c)/n + (log₂|α| + 2)`（`Real.log₂ = Real.log / Real.log 2`）。
- 推奨: `lz78_impl_rate_le_const` の証明内 `hlen`（`bitLength_eq` 展開）+ `hterm1`（`lz78_impl_natLog_mul_log_two_le`）をそのまま切り出して bit 版に。
- 落とし穴: `Nat.log 2 (c+1)` vs `Real.log₂ c` の `+1` ずれ・`c = 0` 退化。

工数感: 全体 ~200–500 行。最大リスクは要素 2（組合せ Ziv の o(n) 制御、D1/D2 回避）。
要素 1・3 は機械的 plumbing。**「もう一本 SMB を建てる」over-estimate は不要**（SMB は既存、
M3 のエルゴード次元は SMB が握っている — roadmap §3 校正）。

---

## Mathlib / in-project 壁の列挙（`@residual` 対象 / genuine 不在）

| 壁 | 不在物 | 確認 | 性質 |
|---|---|---|---|
| **W1 — SMB-in-bits** | `shannon_mcmillan_breiman₂`（`Tendsto blockLogAvg₂ → entropyRate₂`）/ `blockLogAvg₂` def | `rg "blockLogAvg₂"` → コードは prose のみ（`ZivEntropyBridge.lean:256` 等の docstring）、`def`/`lemma` 不在。loogle `InformationTheory.Shannon.blockLogAvg₂` → **unknown identifier**（Found 0 相当） | **wall ではなく plumbing**（既存 `Tendsto.div_const` + `entropyRate₂` def で機械合成可、~30–60 行）。`@residual` 不要、自前 closure 対象 |
| **W2 — a.s.-eventual Ziv 不等式** | `limsup (lz/n) ≤ entropyRate₂` を結論する a.s. 補題（length-grouping overhead o(n) 制御） | コード不在（M3 壁 `lz78GreedyImpl_achievability_ae` 自体）。Mathlib に「LZ78 / Ziv 不等式」は無い | **genuine self-build**（教科書 Cover–Thomas §13.5、未解決ではない）。`@residual(wall:lz78-aseventual-ziv)` の中身そのもの。**共有 sorry-lemma 化は不要**（壁は 1 ファイル 1 箇所、`AsymptoticOptimality.lean:442`） |
| **W3 — D4 dead-start（記録のみ、攻略路でない）** | path-prefix `Q_c = ∏ condPhraseProb` AEP（`∑ⱼqⱼ≈c` trap） | `scripts/dep_consumers.sh InformationTheory.Shannon.blockProb_neg_log_ge_sum` → **direct consumers : 0 decl / 0 file**（dead-start 機械裏取り）。`condPhraseProb` は path-prefix 内部 chain（`prod_condPhraseProb_telescope` / `blockProb_le_prod_condPhraseProb`、`Stationary/Kernel.lean`）のみが参照 = achievability headline へ繋がらない | **攻略 route として推さない**（D4）。length-grouping log-sum を SMB の `-log Pₙ` に直接乗せて素通り |

**loogle 0-hit 確認（settled-facts 用）**:

| query | Found | 解釈 |
|---|---|---|
| `InformationTheory.Shannon.blockLogAvg₂` | unknown identifier（= 0 decl） | `blockLogAvg₂` def 不在 → W1 |
| `InformationTheory.Shannon.entropyRate₂` | Found（def 存在、`EntropyRate.lean:76`） | `entropyRate₂` def は存在 |
| `Filter.Tendsto.limsup_eq` | Found 1（`Mathlib/Topology/Order/LiminfLimsup.lean`） | Step C の核は既存 |
| `Filter.Tendsto.div_const` | Found 1（`Mathlib/Topology/Algebra/GroupWithZero.lean`） | W1 plumbing 既存 |
| `Filter.limsup_le_limsup` | Found 1（`Mathlib/Order/LiminfLimsup.lean`） | Step B の核は既存 |
| `Filter.limsup_le_of_le` | Found 1 | 別ルート既存 |

二段階・結論形検索: 「`Tendsto blockLogAvg₂ → entropyRate₂`」型の補題は `rg "blockLogAvg.*entropyRate₂"`
で **0 hit**（prose 含めても in-project に実 decl 無し）。テンプレ近接補題 = `shannon_mcmillan_breiman`
（nat 版、`Liminf.lean:484`）。これを `/log 2` で bit 化する self-build 行数は ~30–60 行（W1）。

---

## 親プラン撤退ラインへの距離

`docs/shannon/lz78-completion-roadmap.md` §1 M3 / §2 D1–D7 が SoT（撤退ラインは明示的な「○○なら縮退」形では
書かれていないが、go/no-go gate が §3 末尾「M3 = a.s.-eventual Ziv を既証明 SMB に乗せる接続」）。

判定: **触れるが、現時点で発動しない**。

- M3 gate（「`(c·log₂c)/n` を `blockLogAvg₂` に橋渡しする self-contained 比較補題、length-grouping
  overhead で o(n) 制御、D4 trap 回避」）は本在庫が裏付ける既存資産（SMB / Ziv 核 / limsup API）で
  到達可能。**「Mathlib に無いエルゴード定理を一から建てる」基盤コストは無い**（SMB 完成済）。
- 唯一の構造的ギャップ W1（SMB-in-bits 橋）は plumbing 級（~30–60 行）で、撤退ラインを引くほどの壁でない。

ただし以下を **新規撤退ライン候補**として提示（プラン側で採否判断）:

- **M3 着手 ~1 セッション以内に「W1（SMB-in-bits 橋）＋ Step A（符号長 bit-rate を `c·log₂c/n` に展開）」が
  通らない**場合 → 単位整合（nat↔bit）に想定外コストがあるシグナル。その場合の縮退退出は
  **`lz78GreedyImpl_achievability_ae` を `sorry` のまま据え置き、`@residual(wall:lz78-aseventual-ziv)` 維持**
  （hypothesis bundling は禁止 — 退出口は sorry + residual のみ）。length-grouping Ziv 不等式（要素 2）が
  本丸なので、W1 が想定外に重ければ W2 本体に着手する前に gate で止める。
- D1/D2 の per-block 偽性（反例 `a^16`）に抵触する formulation（∀n∀ω の clean / overhead 形）を書いた瞬間に
  即撤退 — a.s.-eventual / limsup 形に戻す。これは撤退ラインではなく不変条件（再探索禁止地雷）。

---

## 着手 skeleton

`InformationTheory/Shannon/LZ78/` に新規ファイル（例 `ZivAchievability.lean`、または既存
`ZivCountingBody.lean` / `AsymptoticOptimality.lean` に追記）の出だし:

```lean
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.SMB.McMillanBreiman      -- shannon_mcmillan_breiman, blockLogAvg
import InformationTheory.Shannon.SMB.AlgoetCover.Liminf   -- (headline は McMillanBreiman 側で十分)
import InformationTheory.Shannon.EntropyRate              -- entropyRate, entropyRate₂
import InformationTheory.Shannon.LZ78.ZivCountingBody     -- lz78PhraseStrings_mul_log_le, count_isBigO
import InformationTheory.Shannon.LZ78.AsymptoticOptimality   -- lz78GreedyImplEncodingLength, lz78_impl_rate_le_const
import Mathlib.Topology.Order.LiminfLimsup                -- Tendsto.limsup_eq, limsup_le_limsup
import Mathlib.Topology.Algebra.GroupWithZero            -- Tendsto.div_const

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **SMB in bits**: `blockLogAvg / Real.log 2` converges a.s. to `entropyRate₂`. -/
noncomputable def blockLogAvg₂
    (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) : Ω → ℝ :=
  fun ω => blockLogAvg μ p n ω / Real.log 2

theorem shannon_mcmillan_breiman₂
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => blockLogAvg₂ μ p.toStationaryProcess n ω)
      Filter.atTop (𝓝 (entropyRate₂ μ p.toStationaryProcess)) := by
  -- W1: shannon_mcmillan_breiman を Tendsto.div_const (Real.log 2) で割り、
  --     entropyRate / Real.log 2 = entropyRate₂ で書換える (~30–60 行、低リスク)
  sorry  -- @residual(plan:lz78-smb-in-bits) — W1 plumbing, not a genuine wall

/-- **a.s.-eventual Ziv comparison**: limsup of the bit-rate is ≤ limsup of blockLogAvg₂. -/
theorem ziv_aseventual_le_blockLogAvg₂
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.limsup
        (fun n => (lz78GreedyImplEncodingLength n
            (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop
      ≤ Filter.limsup
          (fun n => blockLogAvg₂ μ p.toStationaryProcess n ω) Filter.atTop := by
  -- W2 (M3 crux): Step A (bit-rate → c·log₂c/n) + length-grouping overhead o(n)
  --   + limsup_le_limsup. **per-block 形禁止 (D1/D2 FALSE), D4 path-prefix 素通り**.
  sorry  -- @residual(wall:lz78-aseventual-ziv)
```

最後に M3 壁 `lz78GreedyImpl_achievability_ae` を
`filter_upwards [shannon_mcmillan_breiman₂ μ p, ziv_aseventual_le_blockLogAvg₂ μ p]` →
`(h_ziv).trans (h_smb.limsup_eq.le)` で discharge（Step D、~10 行）。

---

## 付記（settled-facts ledger 候補）

- `shannon_mcmillan_breiman` 結論は **nat 単位**（`entropyRate` / `blockLogAvg`）— confidence: machine（`Liminf.lean:488` verbatim Read、再検証 = Read その行）。
- `entropyRate₂ = entropyRate / Real.log 2` は実 def、`blockLogAvg₂` は不在 — confidence: machine + loogle-neg（`rg blockLogAvg₂` prose only / loogle unknown identifier）。
- D4 `blockProb_neg_log_ge_sum` は **0 direct consumers**（dead-start）— confidence: machine（`scripts/dep_consumers.sh` 実測、本セッション）。
- Ziv 定数 K = `8 * Real.log(card α + 1)`（docstring の 4 は誤記）— confidence: machine（`ZivCountingBody.lean:357,194` コード実測）。
</content>
</invoke>
