# Parallel Gaussian Channels + Water-filling ムーンショット計画 🌙 (T2-B)

> **Status (2026-06-13)**: headline `parallel_gaussian_capacity_formula_minimal`
> (`ParallelGaussian/PerCoordRegularity.lean`、hypothesis-minimal 形) は converse #5 closure
> **+ L-WF2 genuine closure** 後、**sorryAx-free**(`#print axioms` = `[propext, Classical.choice,
> Quot.sound]`)。**proof done** — 唯一の入力は `h_kkt` precondition (L-WF1、IVT-dischargeable)。
>
> - **L-WF1** `h_kkt : IsWaterFillingKKT` → discharge 補題**存在** (`KKT.lean`
>   `exists_waterFillingKKT_of_pos`, IVT)。`ν` を pin する precondition として headline に保持
>   (自動適用すると ∃ν 形に変わるため)。
> - **L-WF2** `IsWaterFillingOptimal` → **genuine closure 済** (`KKT.isWaterFillingOptimal_of_kkt`、
>   sorryAx-free、独立監査 `@audit:ok`)。共通 KKT 乗数 `λ=1/(2ν)` での per-coord tangent 上界
>   (`Real.log_le_sub_one_of_pos` 直接ルート) を足し上げ + 相補スラックネス。headline は `h_opt`
>   仮説を drop し本補題で内部供給。子 plan [`parallel-gaussian-wf2-optimality-plan.md`](parallel-gaussian-wf2-optimality-plan.md) DONE。
> - **L-PG0** → `L_PG0Discharge.lean` (kernel measurability) — discharge 済。
> - **L-PG1** → 子 plan [`parallel-gaussian-l-pg1-discharge-plan.md`](parallel-gaussian-l-pg1-discharge-plan.md)、
>   `parallel_gaussian_capacity_formula` (`PerCoord.lean`) は chain-rule plan で genuine
>   `le_antisymm` 着地済 (旧 `:= h_per_coord` pass-through は retracted)。
>
> ⚠️ **経緯 (2026-06-13)**: 本ブロックは一時「全撤退ライン genuine discharge 完了」と記していたが、
> L-WF2 を担う予定だった `WFCertBody`/`WFStationarityBody` が Phase A 補題のみ実装で頓挫し
> `IsWaterFillingOptimal` 産出定理が皆無だったことが発覚 → 一旦「L-WF2 = open/sorry-routed」に訂正 →
> 同日 genuine closure で**真に proof done に到達**(roadmap judgment #28)。空スケルトン
> `WFStationarityBody.lean` + orphan `WFCertBody.lean` は削除。
>
> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 2 — T2-B」
> **Predecessor**: T2-A `AWGN.lean` 完成形 (548 行)、F-* hypothesis pattern 流用元
> **Inventory**: [`parallel-gaussian-mathlib-inventory.md`](parallel-gaussian-mathlib-inventory.md)

## 進捗

- [x] Phase 0 — Mathlib + InformationTheory API 在庫 ✅
- [x] Phase A — `parallelGaussianChannel` + `waterFillingPower` ✅
- [x] Phase B — `parallelGaussianCapacity` 定義 + L-WF1/L-WF2/L-PG1 predicate ✅
- [x] Phase C — 主定理 `parallel_gaussian_capacity_formula` ✅ (旧 pass-through、後に chain-rule plan で genuine 化)
- [x] Phase D — Corollary 群 ✅
- [x] Phase V — verify ✅

## ゴール / Approach

### Goal (publish 時点の surface API)

`namespace InformationTheory.Shannon.ParallelGaussian` 配下:

- `IsParallelAwgnChannelMeasurable N := ∀ i, AWGN.IsAwgnChannelMeasurable (N i)`
- `parallelGaussianChannel N h_meas : Channel (Fin n → ℝ) (Fin n → ℝ)` —
  `toFun x := Measure.pi (gaussianReal (x i) (N i))`、`Markov` instance 付
- `waterFillingPower ν N : Fin n → ℝ := fun i => max 0 (ν - N i)`
- `parallelGaussianCapacity P N h_meas : ℝ` — `sSup` over `∑ ∫ x_i² ≤ P` constraint
- L-WF1 `IsWaterFillingKKT P N ν : Prop := ∑ waterFillingPower ν N = P`
- L-WF2 `IsWaterFillingOptimal P N ν : Prop` — log-sum 最大化解
- L-PG1 `IsParallelGaussianPerCoordReduction P N h_meas ν : Prop` — capacity = water-filling sum 等号
- `parallel_gaussian_capacity_formula` (Cover-Thomas Theorem 9.4.1) —
  当初 `:= h_per_coord` pass-through、後に chain-rule plan で genuine `le_antisymm` 着地
- 新 headline `parallel_gaussian_capacity_formula_minimal` —
  L-PG1 discharge plan で hypothesis-minimal 形に再 publish

### Approach (overall shape)

**2 層構造**: (a) per-coord AWGN closed form (T2-A 再利用) + (b) Lagrange/KKT
power allocation (Mathlib 不在 → L-WF*/L-PG* 撤退ライン)。

**設計選択** (Mathlib-shape-driven):

1. `Measure.pi (gaussianReal ...)` で `Measure.pi_pi` 結論形に直結 (L-PG0 撤退口あり)
2. `max 0 (ν - N_i)` で `max_eq_left/right` 結論形に直結
3. `parallelGaussianCapacity` は T2-A `awgnCapacity` の sSup 形を `Fin n` lift
4. L-WF1/L-WF2/L-PG1 を `Prop` predicate hypothesis 化 (T1-B/T1-C/T2-F/T2-A F-* と同型)、
   主定理本体は `:= h_per_coord` 単独で通る (signature に L-WF1+L-WF2 は textbook 完全形露出のため残置)

### ファイル構成 (publish 後)

新規 `InformationTheory/Shannon/ParallelGaussian.lean` (実績 ~430 行、roadmap 中央予測)。
import: `AWGN`, `AWGNMain`, `ChannelCoding`, `DifferentialEntropy`,
`Mathlib.MeasureTheory.Constructions.Pi`, `Mathlib.Probability.Distributions.Gaussian.Real`。

## 依存関係

- Mathlib: `Gaussian.Real` (`gaussianReal`, `gaussianPDF*`, `rnDeriv_*`, `*_conv_*`,
  `variance_id_*`)、`Constructions.Pi` (`Measure.pi`, `pi_pi`)
- InformationTheory T2-A: `AWGN.lean` 全 API (`awgnChannel`, `awgnCapacity*`,
  `mutualInfoOfChannel_gaussianInput_closed_form`)
- InformationTheory: `ChannelCoding`, `DifferentialEntropy` (Phase D maxent ref)
- 設計参考 (import せず): T2-A `AWGNAchievability/Converse`, T2-F `FisherInfo`,
  T1-B `Chernoff`, T1-C `Cramer` (F-* / L-* hypothesis pattern 流儀)

---

## Phase 0–V (完了)

Phase 0 inventory → Phase A/B/C/D 実装 → Phase V verify、すべて完了。
判断 #1, #2 (`IsParallelAwgnChannelMeasurable := ∀ i, ...` 形 + L-WF1/L-WF2/L-PG1 三本立て
採用) は publish に反映済 (詳細 → 判断ログ)。実装詳細は code (SoT):
`ParallelGaussian/Basic.lean`, `ParallelGaussian/KKT.lean`,
`ParallelGaussian/WFCertBody.lean` (Phase A tangent 補題のみ;
`WFStationarityBody.lean` は空スケルトンのため 2026-06-13 削除),
`ParallelGaussian/L_PG0Discharge.lean`, `ParallelGaussian/PerCoord.lean`,
`ParallelGaussian/PerCoordRegularity.lean`。

---

## 撤退ライン (全 genuine discharge 済)

| Slug | 形 | discharge 経路 | 着地先 file |
|---|---|---|---|
| **L-WF1** | `IsWaterFillingKKT P N ν := ∑ waterFillingPower ν N = P` | IVT + 連続単調増加 | `KKT.lean` (`exists_waterFillingKKT_of_pos`) ✅ |
| **L-WF2** ✅ | water-filling 配分が log-sum 最大化 (`IsWaterFillingOptimal`) | 共通 KKT 乗数 `λ=1/(2ν)` per-coord tangent 上界 (`Real.log_le_sub_one_of_pos` 直接) + 相補スラックネス | `KKT.lean` `isWaterFillingOptimal_of_kkt` (genuine、sorryAx-free、`@audit:ok`)。headline は `h_opt` 仮説 drop し本補題で内部供給 (2026-06-13) |
| **L-PG0** | `Measurable (fun x => Measure.pi (gaussianReal (x i) (N i)))` | `Measure.pi` measurability lift | `ParallelGaussianL_PG0Discharge.lean:98` |
| **L-PG1** | `parallelGaussianCapacity = ∑ (1/2) log(1+waterFilling/N)` (per-coord AWGN bundle) | 子 plan `parallel-gaussian-l-pg1-discharge-plan.md` (sup-sandwich + `le_antisymm` + chain-rule plan) | `ParallelGaussianPerCoord.lean:367` + `ParallelGaussianPerCoordRegularity.lean` (headline minimal) |

残 residual: `h_multivar_decomp` 1 件 (multivariate channel↔RV MI decomposition、別 plan 領域)。

---

## 判断ログ

append-only。

1. **判断 #1 (Phase 0)**: `IsParallelAwgnChannelMeasurable N := ∀ i, IsAwgnChannelMeasurable (N i)`
   形採用。Phase A で `parallelGaussianChannel.measurable'` を per-coord 経由で組む、
   超過時 L-PG0 撤退 → 結果 L-PG0 経路で genuine discharge。
2. **判断 #2 (Phase 0)**: L-WF1 + L-WF2 + L-PG1 三本立て採用 (textbook 完全形露出)。
   本体は L-PG1 単独で済む (`:= h_per_coord`)、L-WF1/L-WF2 は discharge plan bridge
   として signature 保持。
3. **判断 #3 (2026-05-25)**: L-PG1 子 plan で全 Phase genuine 着地、headline を
   hypothesis-minimal 形 (`parallel_gaussian_capacity_formula_minimal`) で再 publish。
   旧 `:= h_per_coord` pass-through は retract、legacy 6 wrappers は
   `@audit:superseded-by(parallel-gaussian-l-pg1-discharge)` 移行 (本体保持)。
4. **判断 #4 (2026-06-13)**: L-WF2 を **load-bearing 仮説 `h_opt` → 撤去し genuine closure**。
   当初 discharge を担うはずだった `WFCertBody`/`WFStationarityBody` が Phase A のみ実装で頓挫
   (空スケルトンの後者 + orphan な前者は削除)、`IsWaterFillingOptimal` 産出定理が皆無だったのを発見
   → 産出定理 `KKT.isWaterFillingOptimal_of_kkt` を新設し capacity formula family から `h_opt` 仮説を drop。
   **同日 genuine 証明まで到達** (sorryAx-free、独立監査 `@audit:ok`): 共通 KKT 乗数 `λ=1/(2ν)` での
   per-coord tangent 上界を `Real.log_le_sub_one_of_pos` で直接導出 (凹 tangent 機構不要) + 相補スラックネス。
   子 plan [`parallel-gaussian-wf2-optimality-plan.md`](parallel-gaussian-wf2-optimality-plan.md) DONE。
   headline `parallel_gaussian_capacity_formula_minimal` は sorryAx-free = proof done。

---

## 子 plan ポインタ

- L-WF2 optimality discharge: [`parallel-gaussian-wf2-optimality-plan.md`](parallel-gaussian-wf2-optimality-plan.md)
  (2026-06-13 **DONE** — `KKT.isWaterFillingOptimal_of_kkt` genuine closure、sorryAx-free、`@audit:ok`)
- L-PG1 discharge: [`parallel-gaussian-l-pg1-discharge-plan.md`](parallel-gaussian-l-pg1-discharge-plan.md)
  (2026-05-25 commit `0fe2ad4` 完了、11 件 closure)
- chain-rule scaffolding: [`parallel-gaussian-chain-rule-plan.md`](parallel-gaussian-chain-rule-plan.md)
  (`PerCoord.lean` genuine `le_antisymm` 着地)
