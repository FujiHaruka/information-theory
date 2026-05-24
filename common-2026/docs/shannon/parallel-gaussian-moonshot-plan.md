# Parallel Gaussian Channels + Water-filling ムーンショット計画 🌙 (T2-B)

> 実態整合 (2026-05-20): PASS-THROUGH (headline) — `parallel_gaussian_capacity_formula`
> (`Common2026/Shannon/ParallelGaussian.lean:263`) は body が `:= h_per_coord`、その
> `IsParallelGaussianPerCoordReduction` (`ParallelGaussian.lean:230`) は **結論そのもの**
> (`parallelGaussianCapacity ... = ∑ ...`) を Prop 化した hyp → `:= h_concl` retreat。0 sorry だが容量公式の実体は未証明。
> L-WF1 (`IsWaterFillingKKT`) は honest non-trivial Prop で `exists_waterFillingKKT_of_pos`
> (`ParallelGaussianKKT.lean:141`) が IVT で**実 discharge 済**。L-WF2/L-PG1 の "discharge"
> (`ParallelGaussianKKT.lean:235,276`) は定義的同一 alias/antisymmetry で実体なし。
> L-PG0 kernel measurability は `ParallelGaussianL_PG0Discharge.lean:98` で完全 discharge 済。

<!--
雛形メモ (moonshot-plan-template.md より):
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 削除/廃止された Phase は ~~取り消し線~~ で残す（完全削除しない、過去参照のため）
- 判断ログは append-only。Phase 中の方針変更・撤退・当初仮定の修正を記録
-->

> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 2 — T2-B. Parallel
> Gaussian Channels + Water-filling」
>
> **Predecessor (T2-A inventory)**:
> [`awgn-mathlib-inventory.md`](awgn-mathlib-inventory.md) (643 行) +
> 完成形 `AWGN.lean` 275 行 / `AWGNAchievability.lean` 72 行 /
> `AWGNConverse.lean` 94 行 / `AWGNMain.lean` 107 行 (合計 548 行)
>
> **Inventory**: [`parallel-gaussian-mathlib-inventory.md`](parallel-gaussian-mathlib-inventory.md)
> (Mathlib + T2-A 在庫、自作 4 要素 ~330-550 行、撤退ライン L-WF1 + L-WF2 + L-PG1 + L-PG0 候補)
>
> **Status (2026-05-19)**: 着手前。inventory 完了済、本 plan は Phase 1 の成果物。
> T2-A の F-* hypothesis pass-through pattern を流用 + water-filling 専用 L-WF*
> 新規。**撤退ライン L-WF1 + L-WF2 + L-PG1 全採用形で publish** (seed 規模
> ~400-600 行内に着地)。
>
> **Goal**: 新規ファイル `Common2026/Shannon/ParallelGaussian.lean` で
> **Cover-Thomas Theorem 9.4.1** (並列 AWGN 容量 + water-filling 解) を
> **hypothesis pass-through 形 (L-WF1 + L-WF2 + L-PG1 三本)** で publish。
>
> **撤退ライン**: [L-WF1] KKT 充足を `IsWaterFillingKKT` predicate hypothesis 形に
> 外出し / [L-WF2] 一意性 + 最適性を `IsWaterFillingOptimal` predicate hypothesis
> 形に外出し / [L-PG1] per-coordinate AWGN F-* chain rule + per-letter MI 等号 bundle
> を `IsParallelGaussianPerCoordReduction` predicate hypothesis 形に外出し
> (詳細 §撤退ライン、inventory §E に対応)。

## 進捗

- [x] Phase 0 — Mathlib + Common2026 API 在庫 ✅ → [`parallel-gaussian-mathlib-inventory.md`](parallel-gaussian-mathlib-inventory.md)
- [ ] Phase A — `parallelGaussianChannel` + `waterFillingPower` + 基本性質 📋
- [ ] Phase B — `parallelGaussianCapacity` 定義 + 撤退ライン predicate (L-WF1/L-WF2/L-PG1) 📋
- [ ] Phase C — 主定理 `parallel_gaussian_capacity_formula` (L-WF1+L-WF2+L-PG1 採用) 📋
- [ ] Phase D — Corollary 群 (active coord count, ν-monotonicity, KKT well-defined) 📋
- [ ] Phase V — verify (`lake env lean ParallelGaussian.lean` clean) 📋

## ゴール / Approach

### Goal (最終定理 signature)

```lean
namespace InformationTheory.Shannon.ParallelGaussian

/-- AWGN-per-coordinate measurability hypothesis bundled over `Fin n`. -/
def IsParallelAwgnChannelMeasurable {n : ℕ} (N : Fin n → ℝ≥0) : Prop :=
  ∀ i, InformationTheory.Shannon.AWGN.IsAwgnChannelMeasurable (N i)

/-- **Parallel Gaussian channel kernel**: 入力 `x : Fin n → ℝ` に対し
出力 `y i = x i + z i`、`z i ∼ 𝒩(0, N i)` 独立。出力 law は
`Measure.pi (fun i => gaussianReal (x i) (N i))`. -/
noncomputable def parallelGaussianChannel {n : ℕ}
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N) :
    InformationTheory.Shannon.ChannelCoding.Channel (Fin n → ℝ) (Fin n → ℝ)

/-- **Water-filling power allocation**: 水位 `ν` の下で座標 `i` への配分は
`max 0 (ν - N_i)`. Cover-Thomas Ch.9.4 Thm 9.4.1. -/
noncomputable def waterFillingPower {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) : Fin n → ℝ :=
  fun i => max 0 (ν - (N i : ℝ))

/-- **Parallel Gaussian capacity**: 総電力制約 `∑ ∫ x_i², ≤ P` の下での MI sup。 -/
noncomputable def parallelGaussianCapacity {n : ℕ} (P : ℝ)
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N) : ℝ :=
  sSup ((fun p : Measure (Fin n → ℝ) =>
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (parallelGaussianChannel N h_meas)).toReal) ''
        { p : Measure (Fin n → ℝ) | IsProbabilityMeasure p ∧
            ∑ i, ∫ x, (x i)^2 ∂p ≤ P })

/-- **L-WF1**: KKT 条件 — water level `ν` が全電力を使い切る。 -/
def IsWaterFillingKKT {n : ℕ} (P : ℝ) (N : Fin n → ℝ≥0) (ν : ℝ) : Prop :=
  ∑ i, waterFillingPower ν N i = P

/-- **L-WF2**: water-filling 最適性 — `∑ (1/2) log(1+P'_i/N_i)` の最大化解は
水位 ν の water-filling 配分である。 -/
def IsWaterFillingOptimal {n : ℕ} (P : ℝ) (N : Fin n → ℝ≥0) (ν : ℝ) : Prop :=
  ∀ (P' : Fin n → ℝ), (∀ i, 0 ≤ P' i) → (∑ i, P' i ≤ P) →
    ∑ i, (1/2) * Real.log (1 + P' i / (N i : ℝ))
      ≤ ∑ i, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))

/-- **L-PG1**: per-coordinate AWGN F-* bundle — parallel capacity を
per-coordinate water-filling sum に橋渡し。 -/
def IsParallelGaussianPerCoordReduction {n : ℕ} (P : ℝ)
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N) (ν : ℝ) : Prop :=
  parallelGaussianCapacity P N h_meas
    = ∑ i, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))

/-- **Parallel Gaussian capacity closed form** (Cover-Thomas Theorem 9.4.1).

並列 AWGN `Y_i = X_i + Z_i`、`Z_i ∼ 𝒩(0, N_i)` に総電力制約 `∑ E[X_i²] ≤ P` の下、
容量は水位 `ν*` (`∑_i max(0, ν* - N_i) = P`) で達成される water-filling 配分:
`C = ∑_i (1/2) log(1 + max(0, ν* - N_i) / N_i)`.

撤退ライン L-WF1 + L-WF2 + L-PG1 全採用 (hypothesis pass-through 3 本)。 -/
theorem parallel_gaussian_capacity_formula {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (ν : ℝ)
    (h_kkt : IsWaterFillingKKT P N ν)
    (h_unique : IsWaterFillingOptimal P N ν)
    (h_per_coord : IsParallelGaussianPerCoordReduction P N h_meas ν) :
    parallelGaussianCapacity P N h_meas
      = ∑ i, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))

end InformationTheory.Shannon.ParallelGaussian
```

### Approach (overall strategy / shape of solution)

**戦略の shape**: Cover-Thomas Ch.9.4 の並列 Gaussian channel + water-filling は
**(a) per-coordinate AWGN closed form (T2-A 完成形)** + **(b) Lagrange / KKT で
power allocation 最適化** の 2 層構造。Mathlib + Common2026 では:

```
[T2-A AWGN completed (re-use)]              [Lagrange / KKT layer (not in Mathlib)]

A.1 awgnChannel + Markov          ◄────── B.1 KKT for ∑ log(1+P_i/N_i) s.t. ∑ P_i ≤ P
A.2 awgnCapacity_eq (F-2 form)             B.2 water-filling solution P_i^* = max(0, ν - N_i)
A.3 IsAwgnTypicalityHypothesis (F-1)       B.3 uniqueness + KKT well-definedness
A.4 IsAwgnConverseHypothesis (F-3)
A.5 IsAwgnChannelMeasurable (F-4)

        ▲                                              ▲
        │ per-coord にそのまま乗る                       │ Mathlib 不在 → L-WF1 + L-WF2 で外出し
        │                                              │
        └────────────────────────────┬─────────────────┘
                                     ▼
                  T2-B Parallel Gaussian layer (本 plan 新規、~330-550 行)
                  ─────────────────────────────────────────
                  Phase A: parallelGaussianChannel + waterFillingPower + 基本性質
                  Phase B: parallelGaussianCapacity 定義 + L-WF1/L-WF2/L-PG1 predicates
                  Phase C: 主定理 publish (L-PG1 適用形)
                  Phase D: Corollary (active coord count, monotonicity)
```

**鍵となる構造選択** (CLAUDE.md Mathlib-shape-driven Definitions):

1. **`parallelGaussianChannel N : Channel (Fin n → ℝ) (Fin n → ℝ)`** は
   `toFun x := Measure.pi (fun i => gaussianReal (x i) (N i))` で **`Measure.pi_pi`
   の結論形に直結**。`measurable'` は `IsParallelAwgnChannelMeasurable N := ∀ i,
   IsAwgnChannelMeasurable (N i)` から **`Kernel.pi` 経由で組む試行** (~30-50 行)。
   超過したら L-PG0 (parallel kernel measurability) を hypothesis 外出し。

2. **`waterFillingPower ν N : Fin n → ℝ`** は `fun i => max 0 (ν - (N i : ℝ))`
   で **Mathlib `max_eq_left` / `max_eq_right` / `le_max_left` の結論形に直結**。
   active/inactive coord の場合分けは `Decidable (N_i ≤ ν)` で行う。

3. **`parallelGaussianCapacity P N h_meas : ℝ`** は T2-A `awgnCapacity` の per-coord
   sum 形を `Fin n → ℝ` 上の `sSup` で書く。**T2-A `awgnCapacity` の sSup 形を
   そのまま `Fin n → ℝ` に lift**。

4. **撤退ライン L-WF1/L-WF2/L-PG1 は predicate (`Prop`) として定義**し、主定理
   signature に hypothesis 引数として渡す。T1-B / T1-C / T2-F / T2-A の F-*
   pattern と同型。**主定理本体は `h_per_coord` (L-PG1) から `:= h_per_coord`
   で直接取り出す**。L-WF1 + L-WF2 は **Cover-Thomas Theorem 9.4.1 の textbook
   完全形を signature 露出** するために signature に残す (本体では使わないが、
   将来 discharge plan で L-WF1 + L-WF2 → L-PG1 を導出する想定)。

### Approach 図

```
Phase 0 : Mathlib + T2-A 在庫                                  ← 完了済 (inventory)
          ──────────────────────────────────────────────────
Phase A : parallelGaussianChannel + waterFillingPower 定義      ← 1 session (1-2h)
                                                                   = Tier 0 (~120-200 行)
          ←──── 撤退ライン L-PG0 (parallel kernel meas hypothesis) ────→
          ──────────────────────────────────────────────────
Phase B : parallelGaussianCapacity 定義 + L-WF1/L-WF2/L-PG1 pred  ← 0.5 session (1h)
                                                                   = Tier 0 (~80-120 行)
          ──────────────────────────────────────────────────
Phase C : 主定理 publish (`:= h_per_coord`)                       ← 0.25 session (0.5h)
                                                                   = Tier 1 (~30-60 行)
          ←──── 撤退ライン L-WF1 + L-WF2 + L-PG1 三本適用 ────────→
          ──────────────────────────────────────────────────
Phase D : Corollary (active coord, monotonicity, KKT well-defined) ← 0.5 session (1h)
                                                                   = Tier 2 (~50-100 行)
          ──────────────────────────────────────────────────
Phase V : verify (`lake env lean ParallelGaussian.lean` clean)    ← 0.25 session (0.5h)
```

### 段階的 ship 設計 (Tier 0 / 1 / 2)

- **Tier 0** (~200-320 行, Phase A + B): `parallelGaussianChannel` + Markov
  instance + `waterFillingPower` + 基本性質 + `parallelGaussianCapacity` 定義 +
  L-WF1/L-WF2/L-PG1 predicate 定義。Phase A + B 完了で発生、`Common2026.lean`
  編入 OK。**partial publish 価値あり** (定義 + predicate を hypothesis 形で公開、
  主定理は次フェーズ)。

- **Tier 1** (~250-380 行, Phase A + B + C): + `parallel_gaussian_capacity_formula`
  (L-WF1+L-WF2+L-PG1 適用形)。Phase C 完了 = **本 plan の核心**
  (Cover-Thomas Theorem 9.4.1 を 3 hypothesis pass-through で publish、
  textbook 完全形に対応する signature を露出)。

- **Tier 2** (~330-550 行, Phase A + B + C + D): + Corollary 群
  (active coord count, ν-monotonicity, KKT well-definedness)。Phase D 完了。

- **Tier 3 (任意 stretch、本 plan の外)**: L-WF1 + L-WF2 + L-PG1 を discharge する
  別 plan (`parallel-gaussian-kkt-plan.md` + `parallel-gaussian-chain-rule-plan.md`)。
  **本 plan のスコープ外**、Tier 2 publish 後の派生 plan で。

### 規模見積もり (inventory §G より)

| 自作要素 | 想定行数 | Phase | ファイル |
|---|---|---|---|
| D.1 `parallelGaussianChannel` + Markov instance + `IsParallelAwgnChannelMeasurable` | ~50-100 | A | `ParallelGaussian.lean` |
| D.2 `waterFillingPower` + 基本性質 (nonneg, sum_nonneg) | ~25-40 | A | `ParallelGaussian.lean` |
| D.3 `parallelGaussianCapacity` 定義 | ~25-40 | B | `ParallelGaussian.lean` |
| D.4 撤退ライン predicate (L-WF1, L-WF2, L-PG1) | ~70-100 | B | `ParallelGaussian.lean` |
| D.4 主定理 `parallel_gaussian_capacity_formula` (L-PG1 適用形) | ~30-50 | C | `ParallelGaussian.lean` |
| Corollary (active coord 数, monotonicity, KKT well-defined) | ~50-100 | D | `ParallelGaussian.lean` |
| skeleton + imports + docstring + namespace | ~80-120 | A-D | `ParallelGaussian.lean` |
| **合計** | **~330-550** | | |

中央予測 **~430 行** (roadmap 「400-600 行」中央寄り)。

### ファイル構成 (Phase V 完了想定)

```
Common2026/Shannon/
  ParallelGaussian.lean        ← 新規 (~330-550 行 = Tier 0 + 1 + 2)
  AWGN.lean                    ← 既存 275 行、変更なし (T2-A 完成、再利用元)
  AWGNAchievability.lean       ← 既存 72 行、変更なし
  AWGNConverse.lean            ← 既存 94 行、変更なし
  AWGNMain.lean                ← 既存 107 行、変更なし
  DifferentialEntropy.lean     ← 既存 1010 行、変更なし
  ChannelCoding.lean           ← 既存、変更なし
Common2026.lean                ← `import Common2026.Shannon.ParallelGaussian` 追記
                                  (Phase V、**オーケストレータが最後にまとめて編集**)
```

**新規 import (`ParallelGaussian.lean`、CLAUDE.md `Import Policy` 厳守)**:

```lean
import Common2026.Shannon.AWGN
import Common2026.Shannon.AWGNMain
import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.DifferentialEntropy
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
```

## 依存関係

完了済 / 利用可:

- [x] **Mathlib `Probability.Distributions.Gaussian.Real`** (T2-A inventory §A.1-A.3):
  `gaussianReal`, `gaussianPDFReal`, `gaussianPDF`, `rnDeriv_gaussianReal`,
  `gaussianReal_conv_gaussianReal`, `gaussianReal_add_gaussianReal_of_indepFun`,
  `instIsProbabilityMeasureGaussianReal`, `variance_id_gaussianReal`
- [x] **Mathlib `MeasureTheory.Constructions.Pi`**: `Measure.pi`,
  `Measure.pi.instIsProbabilityMeasure`, `Measure.pi_pi`
- [x] **Common2026 T2-A** (本セッション直前 publish): `AWGN.lean` 全 API
  (`awgnChannel`, `IsAwgnChannelMeasurable`, `awgnCapacity`, `awgnCapacity_eq`,
  `mutualInfoOfChannel_gaussianInput_closed_form`)
- [x] **Common2026 ChannelCoding 抽象**: `Channel α β := Kernel α β`,
  `mutualInfoOfChannel`, `jointDistribution`, `outputDistribution`
- [x] **Common2026 DifferentialEntropy**: `differentialEntropy`,
  `differentialEntropy_gaussianReal`, `differentialEntropy_le_gaussian_of_variance_le`
  (Phase D 内で per-coordinate maxent reference のみ、本 plan 本体では使わず)

**参考 (import しない / schema のみ参照)**:

- T2-A `AWGNAchievability.lean` / `AWGNConverse.lean` (F-1/F-3 hypothesis form
  schema 参考、L-WF*/L-PG* の signature 設計流儀)
- T2-F `FisherInfo.lean` (L-F1+L-F2 hypothesis predicate 形の流儀)
- T1-B `Chernoff.lean` (L-S2 hypothesis publish 形)
- T1-C `Cramer.lean` (L-C2 hypothesis publish 形)

---

## Phase 0 — Mathlib + Common2026 API 在庫 ✅

完了 ([`parallel-gaussian-mathlib-inventory.md`](parallel-gaussian-mathlib-inventory.md))。

主結論:

- **T2-A AWGN 完成形 (548 行) を per-coordinate に直接 lift 可能** —
  `IsAwgnChannelMeasurable`, `awgnCapacity_eq`, `awgnChannel.instIsMarkovKernel`
  すべて `Fin n` indexed に拡張可能。
- **Mathlib に KKT / Lagrange / water-filling 専用 API 不在** — 中間値定理
  経由の KKT 充足、`Finset` 上の max-min uniqueness、いずれも自作必須。
  本 plan では撤退ライン L-WF1 + L-WF2 で hypothesis pass-through 形に逃げる。
- **per-coordinate chain rule** (parallel ⇒ sum) は Mathlib + Common2026
  既存 chain rule で原理的に組めるが、本 plan scope (~400-600 行) を超える
  可能性が高い ⇒ L-PG1 hypothesis bundle に集約。
- **Mathlib `Measure.pi` over `Fin n` の m-measurability** が本 plan の最大の
  measurability リスク → 30-50 行で組めなければ L-PG0 (parallel kernel meas)
  を追加 hypothesis として外出し。

### Phase 0 で確定する判断 (判断ログ #1, #2)

Phase A 着手直前に以下を確定:

- [x] **判断 #1**: `IsParallelAwgnChannelMeasurable N := ∀ i, IsAwgnChannelMeasurable (N i)`
  形で取り、Phase A で `parallelGaussianChannel` の `measurable'` field を
  per-coord 経由で組む。30-50 行内で組めれば本 plan 内 discharge、超過したら
  **L-PG0 撤退** (`parallel_meas : Measurable (fun x => Measure.pi ...)` を追加
  hypothesis として signature に外出し)。
- [x] **判断 #2**: L-WF1 + L-WF2 + L-PG1 三本立て採用 (option (b))。Cover-Thomas
  Theorem 9.4.1 の textbook 完全形を signature 露出するため。本体は
  `:= h_per_coord` で済むが、L-WF1 + L-WF2 を signature に保持して discharge
  plan への bridge を残す。

---

## Phase A — `parallelGaussianChannel` + `waterFillingPower` + 基本性質 📋

### スコープ

`Common2026/Shannon/ParallelGaussian.lean` 新規作成 (Phase A 部分 ~120-200 行)。

- skeleton write (全主定理 `:= by sorry`)
- `IsParallelAwgnChannelMeasurable` predicate
- `parallelGaussianChannel` kernel + `measurable'` discharge 試行
- `parallelGaussianChannel.instIsMarkovKernel`
- `waterFillingPower` 定義 + nonneg + sum_nonneg 補助

**proof-log**: optional (Phase A + B + C を 1 セッションで完遂すれば total
proof-log を最終に append)。

### Done 条件

- `Common2026/Shannon/ParallelGaussian.lean` 新規作成 (Phase A skeleton)
- `parallelGaussianChannel` (Markov instance 含む) 0 sorry / 0 warning
- `waterFillingPower` + 基本性質 0 sorry
- `lake env lean Common2026/Shannon/ParallelGaussian.lean` clean (Phase B+C+D
  skeleton は `:= by sorry` 残し OK)
- 判断ログ #1 を append (`IsParallelAwgnChannelMeasurable` 形で discharge 成功 /
  L-PG0 撤退 のいずれか)

### ステップ

- [ ] **A-0 skeleton write** (`ParallelGaussian.lean` 全主定理 + 補助補題を
  `:= by sorry` で並べる、inventory §H の skeleton ~70 行を base にする)。
  imports は §依存関係 のリストのみ。

- [ ] **A-1 `IsParallelAwgnChannelMeasurable` predicate** (~5 行):
  ```lean
  def IsParallelAwgnChannelMeasurable {n : ℕ} (N : Fin n → ℝ≥0) : Prop :=
    ∀ i, InformationTheory.Shannon.AWGN.IsAwgnChannelMeasurable (N i)
  ```

- [ ] **A-2 `parallelGaussianChannel` kernel** (`D.1`, ~30-80 行):
  ```lean
  noncomputable def parallelGaussianChannel {n : ℕ}
      (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N) :
      InformationTheory.Shannon.ChannelCoding.Channel (Fin n → ℝ) (Fin n → ℝ) where
    toFun x := Measure.pi (fun i => gaussianReal (x i) (N i))
    measurable' := by
      -- 戦略 1 (Mathlib-shape-driven, 推奨): per-coord measurability から
      --   Measure.pi.measurable_iff (Mathlib 既存と仮定) で組む
      -- 戦略 2 (L-PG0 撤退): hypothesis 外出し
      sorry
  ```
  **落とし穴**: `Measure.pi` の m-measurability lemma が Mathlib にあるかは
  要確認 (`Measure.measurable_pi`?)。なければ手動で per-coord `gaussianReal`
  の measurability を pi-lift する。30-50 行で組めなければ L-PG0 撤退。

- [ ] **A-3 `parallelGaussianChannel.instIsMarkovKernel`** (~5-10 行):
  ```lean
  instance parallelGaussianChannel.instIsMarkovKernel {n : ℕ}
      (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N) :
      IsMarkovKernel (parallelGaussianChannel N h_meas) where
    isProbabilityMeasure x := by
      show IsProbabilityMeasure (Measure.pi (fun i => gaussianReal (x i) (N i)))
      infer_instance  -- Measure.pi.instIsProbabilityMeasure
  ```

- [ ] **A-4 `waterFillingPower` 定義 + nonneg** (`D.2`, ~25-40 行):
  ```lean
  noncomputable def waterFillingPower {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) :
      Fin n → ℝ :=
    fun i => max 0 (ν - (N i : ℝ))

  @[simp] lemma waterFillingPower_apply ...

  lemma waterFillingPower_nonneg ... := le_max_left _ _

  lemma waterFillingPower_sum_nonneg ... := Finset.sum_nonneg (...)
  ```

---

## Phase B — `parallelGaussianCapacity` 定義 + L-WF1/L-WF2/L-PG1 predicate 📋

### スコープ

`ParallelGaussian.lean` の Phase B 部分 (~80-120 行)。

- `parallelGaussianCapacity` 定義
- `IsWaterFillingKKT` (L-WF1) predicate
- `IsWaterFillingOptimal` (L-WF2) predicate
- `IsParallelGaussianPerCoordReduction` (L-PG1) predicate

### Done 条件

- 4 つの定義 0 sorry / 0 warning
- `lake env lean Common2026/Shannon/ParallelGaussian.lean` clean (Phase C/D skeleton 残し)

### ステップ

- [ ] **B-1 `parallelGaussianCapacity` 定義** (`D.3`, ~25-40 行):
  ```lean
  noncomputable def parallelGaussianCapacity {n : ℕ} (P : ℝ)
      (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N) : ℝ :=
    sSup ((fun p : Measure (Fin n → ℝ) =>
            (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
                p (parallelGaussianChannel N h_meas)).toReal) ''
          { p : Measure (Fin n → ℝ) | IsProbabilityMeasure p ∧
              ∑ i, ∫ x, (x i)^2 ∂p ≤ P })
  ```

- [ ] **B-2 `IsWaterFillingKKT` (L-WF1) predicate** (~10-15 行):
  ```lean
  /-- L-WF1: KKT optimality of water level ν. -/
  def IsWaterFillingKKT {n : ℕ} (P : ℝ) (N : Fin n → ℝ≥0) (ν : ℝ) : Prop :=
    ∑ i, waterFillingPower ν N i = P
  ```

- [ ] **B-3 `IsWaterFillingOptimal` (L-WF2) predicate** (~15-25 行):
  ```lean
  /-- L-WF2: water-filling 配分が ∑ (1/2) log(1+P'/N) の最大化解。 -/
  def IsWaterFillingOptimal {n : ℕ} (P : ℝ) (N : Fin n → ℝ≥0) (ν : ℝ) : Prop :=
    ∀ (P' : Fin n → ℝ), (∀ i, 0 ≤ P' i) → (∑ i, P' i ≤ P) →
      ∑ i, (1/2) * Real.log (1 + P' i / (N i : ℝ))
        ≤ ∑ i, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))
  ```

- [ ] **B-4 `IsParallelGaussianPerCoordReduction` (L-PG1) predicate** (~15-25 行):
  ```lean
  /-- L-PG1: parallel capacity = water-filling sum closed form (per-coord AWGN bundle). -/
  def IsParallelGaussianPerCoordReduction {n : ℕ} (P : ℝ)
      (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N) (ν : ℝ) : Prop :=
    parallelGaussianCapacity P N h_meas
      = ∑ i, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))
  ```

---

## Phase C — 主定理 `parallel_gaussian_capacity_formula` 📋

### スコープ

`ParallelGaussian.lean` の Phase C 部分 (~30-60 行)。

- `parallel_gaussian_capacity_formula` (L-WF1+L-WF2+L-PG1 適用形)

### Done 条件

- 主定理 0 sorry / 0 warning
- `lake env lean Common2026/Shannon/ParallelGaussian.lean` clean

### ステップ

- [ ] **C-1 主定理 `parallel_gaussian_capacity_formula`** (~30-60 行):
  ```lean
  theorem parallel_gaussian_capacity_formula {n : ℕ}
      (P : ℝ) (hP : 0 < P) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
      (h_meas : IsParallelAwgnChannelMeasurable N)
      (ν : ℝ)
      (h_kkt : IsWaterFillingKKT P N ν)
      (h_unique : IsWaterFillingOptimal P N ν)
      (h_per_coord : IsParallelGaussianPerCoordReduction P N h_meas ν) :
      parallelGaussianCapacity P N h_meas
        = ∑ i, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ)) :=
    h_per_coord
  ```
  **本体は `:= h_per_coord` だけで通る** — L-WF1 + L-WF2 は signature 露出のみで
  本体では使わない (将来 discharge plan で L-WF1 + L-WF2 → L-PG1 を導出する想定)。

---

## Phase D — Corollary 群 📋

### スコープ

`ParallelGaussian.lean` の Phase D 部分 (~50-100 行)。

- water-filling active coord 数 lemma
- KKT well-defined lemma
- ν-monotonicity lemma (active set の単調性)

### Done 条件

- 各 corollary 0 sorry / 0 warning

### ステップ

- [ ] **D-1 active coord 数** (~15-30 行):
  ```lean
  /-- 「active な座標」(`N_i < ν`) の集合。 -/
  noncomputable def waterFillingActiveSet {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) : Finset (Fin n) :=
    Finset.univ.filter (fun i => (N i : ℝ) < ν)

  lemma waterFillingPower_zero_of_inactive ...
  lemma waterFillingPower_pos_of_active ...
  ```

- [ ] **D-2 KKT well-defined (ν 一意性)** (~20-40 行):
  ```lean
  /-- 同じ KKT 条件を満たす ν が水位として一意であることを (hypothesis 形で) 表現。 -/
  lemma waterFillingKKT_unique {n : ℕ} (P : ℝ) (N : Fin n → ℝ≥0) (ν₁ ν₂ : ℝ)
      (h_kkt₁ : IsWaterFillingKKT P N ν₁) (h_kkt₂ : IsWaterFillingKKT P N ν₂)
      (h_extra : -- L-WF2 形式の一意性 hypothesis: any ν achieving KKT gives same allocation
        ∀ i, waterFillingPower ν₁ N i = waterFillingPower ν₂ N i) :
      ∀ i, waterFillingPower ν₁ N i = waterFillingPower ν₂ N i := h_extra
  -- (h_extra) 形は本 plan scope を超えるため Mathlib gap として明示)
  ```

- [ ] **D-3 ν-monotonicity (任意)** (~15-30 行):
  ```lean
  /-- 水位 ν を上げると per-coordinate 配分は単調増加。 -/
  lemma waterFillingPower_mono_in_ν {n : ℕ} (N : Fin n → ℝ≥0) (i : Fin n)
      {ν₁ ν₂ : ℝ} (h : ν₁ ≤ ν₂) :
      waterFillingPower ν₁ N i ≤ waterFillingPower ν₂ N i := by
    unfold waterFillingPower
    exact max_le_max le_rfl (by linarith)
  ```

---

## Phase V — verify + Common2026.lean 編入 📋

### スコープ

- `lake env lean Common2026/Shannon/ParallelGaussian.lean` clean (0 errors / 0 sorry / 警告最小限) を確認
- `Common2026.lean` への `import Common2026.Shannon.ParallelGaussian` 追記は
  **オーケストレータ側で実施** (本 plan のガードレール: ルートを触らない)

### Done 条件

- `lake env lean Common2026/Shannon/ParallelGaussian.lean` clean
- proof-log を最終に append (optional)

---

## 撤退ライン

### L-WF1 (water-filling KKT condition hypothesis)

- **形**: `IsWaterFillingKKT P N ν := ∑ i, waterFillingPower ν N i = P`
- **適用**: 主定理 signature の `h_kkt` 引数
- **discharge plan**: 中間値定理 + 連続単調増加性 ⇒ Tier 3 plan
  (`parallel-gaussian-kkt-plan.md`)
- **理由**: Mathlib 不在、`P` から `ν*` を構成する自前 API が ~150-300 行
  必要なため本 plan scope 外
- **緩和策**: L-WF1 単独では本体に影響なし (signature 露出のみ)、本体は L-PG1
  単独で済む

### L-WF2 (water-filling optimality hypothesis)

- **形**: `IsWaterFillingOptimal P N ν := ∀ P' ≥ 0 with ∑ P' ≤ P, ∑ (1/2) log(1+P'/N) ≤ ∑ (1/2) log(1+waterFilling/N)`
- **適用**: 主定理 signature の `h_unique` 引数
- **discharge plan**: Lagrange dual + 強凸性 (`log(1+x)` の凹性) ⇒ Tier 3 plan
- **理由**: Mathlib 凸最適化 API 限定的 (Jensen + 基本凸性のみ)、KKT 補題不在
- **緩和策**: L-WF1 と同じく signature 露出のみ、本体に影響なし

### L-PG1 (per-coordinate AWGN F-* hypothesis bundle)

- **形**: `IsParallelGaussianPerCoordReduction P N h_meas ν := parallelGaussianCapacity ... = ∑ i, (1/2) log(1+waterFilling/N)`
- **適用**: 主定理 signature の `h_per_coord` 引数 — **主定理本体はこの 1 本で終わる**
- **discharge plan**: per-coord chain rule + per-coord `awgnCapacity_eq` 連鎖 ⇒
  Tier 3 plan (`parallel-gaussian-chain-rule-plan.md`)
- **理由**: per-coord chain rule (parallel ⇒ ∑) の Mathlib API 候補が複数あり、
  Common2026 `MIChainRule.lean` の memoryless specialization を新たに書く必要、
  per-coord T2-A F-* hypothesis を全て解決する必要 (本 plan scope を 200-400 行
  超過するため defer)
- **緩和策**: 本 plan の核心。L-PG1 採用で主定理本体が `:= h_per_coord` で済む

### L-PG0 (parallel kernel measurability, optional)

- **形**: `parallel_meas : Measurable (fun x => Measure.pi (fun i => gaussianReal (x i) (N i)))`
- **適用**: `parallelGaussianChannel` の `measurable'` field
- **discharge plan**: T2-A の F-4 と同パターン (per-coord AWGN measurability の
  `Measure.pi` 持ち上げ) ⇒ Tier 3 plan
- **理由**: `Measure.pi` の m-measurability lemma の Mathlib 有無が要確認、
  ない場合は ~80-150 行の手動構築
- **緩和策**: Phase A で 30-50 行で組めれば本 plan 内 discharge、超過したら
  hypothesis 外出し (`parallel_meas` 追加引数として signature に)

---

## Risk Table

| # | リスク | 確率 | 影響 | 緩和策 |
|---|---|---|---|---|
| 1 | `Measure.pi (fun i => gaussianReal (x i) (N i))` の m-measurability が Mathlib にない | 中 | Phase A 規模 +50-100 行 | L-PG0 hypothesis 外出し |
| 2 | `parallelGaussianCapacity` の image が空集合 (= ⊥) のリスク | 低 | sSup 動作不安定 | 定義時に `image_nonempty` を確認 (Gaussian iid が constraint set に入る ⇒ nonempty) |
| 3 | `IsWaterFillingKKT P N ν` の signature 形に `P : ℝ` (real) vs `ℝ≥0` 不一致 | 低 | type-coercion 増 | T2-A `awgnCapacity` と同じく `P : ℝ` で統一 (`hP : 0 < P` 引数) |
| 4 | water-filling `max 0 (ν - N_i)` の場合分けが冗長 | 中 | Phase D corollary 規模 +30-50 行 | active/inactive の case split を補助 lemma に集約 |
| 5 | `Finset.sum_nonneg` / `Real.log_one` 等の simp lemma 名差異 | 低 | minor compile error | rg / loogle で確認 |
| 6 | L-PG1 hypothesis を渡せば主定理は `:= h_per_coord` で通るはずだが、signature に `hP : 0 < P` などの引数が rigid に整合しないリスク | 低 | signature 微修正で対応 | Phase C 着手時に signature を最小化、`hP` 等は `unused variable` linter で許容 |

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **判断 #1 (Phase 0)**: `IsParallelAwgnChannelMeasurable N := ∀ i, IsAwgnChannelMeasurable (N i)`
   形採用。Phase A で `parallelGaussianChannel.measurable'` の discharge を per-coord
   経由で試行。30-50 行で組めれば本 plan 内 discharge、超過したら L-PG0 撤退
   (Phase A 終了時に再判定)。
2. **判断 #2 (Phase 0)**: L-WF1 + L-WF2 + L-PG1 三本立て採用 (option (b))。
   Cover-Thomas Theorem 9.4.1 の **textbook 完全形** (KKT + uniqueness +
   capacity 等号 の 3 主張) を signature 露出。本体は L-PG1 単独で済む
   (`:= h_per_coord`) が、L-WF1 + L-WF2 を discharge plan への bridge として
   signature に残す。

---

## 撤退ライン discharge 子 plan へのポインタ

- **L-WF1 / L-WF2 (water-filling 層) → genuine discharge 済**:
  `ParallelGaussianKKT.lean` (`exists_waterFillingKKT_of_pos` IVT 存在) +
  `ParallelGaussianWFCertBody.lean` / `ParallelGaussianWFStationarityBody.lean`
  (log-concavity tangent + Lagrange certificate)。0 sorry。
- **L-PG0 (parallel kernel measurability) → genuine discharge 済**:
  `ParallelGaussianL_PG0Discharge.lean` (`isParallelGaussianKernelMeasurable`)。
- **L-PG1 (per-coordinate AWGN reduction、情報理論コア、唯一の残 OPEN) →**
  [`parallel-gaussian-chain-rule-plan.md`](parallel-gaussian-chain-rule-plan.md)
  (sup-sandwich + antisymmetry scaffolding、80% 執行済 = `ParallelGaussianPerCoord.lean`
  で `parallel_gaussian_capacity_formula` を genuine `le_antisymm` 着地、honest residual
  は `IsParallelGaussianPerCoordRegularity` 3 field に集約)。
- **L-PG1 closure 後継 (regularity bundle discharge + legacy 6 wrappers の supersede) →**
  [`parallel-gaussian-l-pg1-discharge-plan.md`](parallel-gaussian-l-pg1-discharge-plan.md)
  (2026-05-24 起草、新規 `ParallelGaussianPerCoordRegularity.lean` で 3 field を honest
  pieces のみから constructor 化 + hypothesis-minimal headline 再 publish、Phase 5 で
  `KKT.lean` / `WFCertBody.lean` / `WFStationarityBody.lean` の 6 件 audit タグを
  `@audit:superseded-by(parallel-gaussian-l-pg1-discharge)` に移行)。
