# AWGN Achievability — typicality discharge ムーンショット計画 🌙 (T2-A Tier-3 follow-up)

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) F-1。
> **Sibling**: [`awgn-f1-discharge-moonshot-plan.md`](awgn-f1-discharge-moonshot-plan.md) (F-4, done) / `awgn-mi-bridge-plan.md` (F-2, 未起草) / `awgn-converse-aux-plan.md` (F-3, 未起草)。
> **Status**: **完走 (2026-05-24)** — `AWGNAchievabilityDischarge.lean` 1641 行 / 0 sorry / silent / 2 honest staged hyps (continuous-aep-gaussian + awgn-random-coding-feasible bundle)。

## 進捗 ✅

- [x] Phase 0 — inventory ([`...-mathlib-inventory.md`](awgn-achievability-typicality-mathlib-inventory.md) + 5 軸別 file)、判断 #1-#3 確定
- [x] Phase A — `gaussianCodebook` + IndepFun (`8c1bc4d`)
- [x] Phase B-0 — `IsContinuousAEPGaussian` staged (`8c1bc4d`)
- [x] Phase C — decoder + `IsAwgnRandomCodingBound` (`83c23ab`)
- [x] Phase D — expurgation + `IsAwgnPowerConstraintRealizable` (`ccd503f`)
- [x] Phase E — 統合 + wrapper (`e9058ad`)
- [x] Phase V — verify + `InformationTheory.lean` 編入
- [x] Phase Pivot — bundle pivot (false-statement defect 修正、判断ログ #7、sibling [`awgn-power-constraint-realizable-pivot-plan.md`]、`9dcef00` / `2ace40b` / `c02304c`)

## ゴール / Approach (anchor、完了)

`AWGNAchievabilityDischarge.lean` に publish 済の最終 signature:

- `isAwgnTypicalityHypothesis` — F-1 discharge (Cover-Thomas 9.2)、staged hyp = `IsContinuousAEPGaussian` + `IsAwgnRandomCodingFeasible` (bundle)
- `awgn_achievability_F1_discharged` / `awgn_theorem_F1F4_discharged` — wrapper、残 hyp = F-2 + F-3 + staged 2 本

戦略 = Cover-Thomas 9.2 の 4 段 (A random codebook → B continuous AEP → C union bound → D expurgation → E 統合) を 1 file 直転写。Mathlib-shape は判断 #2 (codebook = 2 段 `Measure.pi`) + #3 (typical set = `klDiv` 形) で確定。詳細 → 判断ログ #1-#7。

## Phase 0-E (anchor、全完了)

各 Phase の scope / 採用 lemma / trap / 工数感は判断ログ #1-#7 で resolved。再起動時は判断ログ参照。

- Phase 0: inventory 5 軸別 file (合計 2968 行)、判断 #1 (T-2 採用) + #2 (Option A) + #3 (Option γ klDiv)
- Phase A: `gaussianCodebook` + IndepFun (Mathlib 100% 既存、`8c1bc4d`)
- Phase B-0: `IsContinuousAEPGaussian` predicate (`@audit:staged(continuous-aep-gaussian)`)
- Phase C: jointTypicalDecoder + `IsAwgnRandomCodingBound` (`83c23ab`)
- Phase D: D-1/D-2/D-3 publish 0 sorry (`exists_le_lintegral` + Finset arithmetic + AwgnCode constructor、`ccd503f`)
- Phase E: 統合 + 2 wrapper (`e9058ad`、E-1 body ~580 行 + Kernel.pi helper ~170 行)
- Phase V: silent / 0 sorry / `InformationTheory.lean` 編入


## 撤退ライン / Risk (resolved、参考)

完走で全 risk resolved。発動結果:

- **T-2 採用** (continuous AEP Mathlib 不在) → `IsContinuousAEPGaussian` regularity hyp 化、achievability core は genuine discharge (判断 #1)
- **T-1 不発動** (Option A 2 段 `Measure.pi` で型クラス通過、判断 #2)
- **T-3 不発動** (`exists_le_lintegral` 直接使用、Phase D-1)
- **T-4 不発動** (1641 行 1 file 集約で完走)
- **Pivot 発動**: `IsAwgnPowerConstraintRealizable` v1 が false-statement defect → bundle 形に統合 (判断 #7、sibling [`awgn-power-constraint-realizable-pivot-plan.md`])

**honesty 撤退ライン** (常時規律): name laundering 禁止 / staged hyp は (a) 結論型と異なる + (b) docstring で NOT load-bearing 明記 + (c) core は genuine discharge + (d) `@audit:staged` タグ。Phase V re-audit 通過。

## 親 plan / 兄弟 plan

| Plan | scope | 出力 | 状態 |
|---|---|---|---|
| `awgn-moonshot-plan.md` (親) | T2-A 全体 | AWGN.lean + 3 sibling | DONE |
| `awgn-f1-discharge-moonshot-plan.md` | **F-4** (kernel measurability、seed 名 F-1) | `AWGNF1Discharge.lean` 148 | DONE |
| **本 plan** | **F-1** (typicality/achievability core) | `AWGNAchievabilityDischarge.lean` 1641 | **DONE** |
| `awgn-mi-bridge-plan.md` | F-2 (MI bridge) | TBD | 未起草 |
| `awgn-converse-aux-plan.md` | F-3 (per-letter integrability) | TBD | 未起草 |

注: sibling seed 名「F-1」は親番号体系の **F-4**、本 plan は親の **F-1** — 別物。


## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### #1 (2026-05-24) Phase 0 完了、T-2 採用 (`IsContinuousAEPGaussian` regularity hyp 化)

Axis 2 inventory ([`...-axis2-aep.md`](awgn-achievability-typicality-mathlib-inventory-axis2-aep.md)): Mathlib に continuous AEP 本体 / n-d differentialEntropy / continuous SMB が不在、SLLN 1-d は既存。T-2 不採用ルート Phase B ~390 行 + 全体 750-810 → T-4 高確率 → 却下。T-2 採用ルート Phase B ~50 行 (predicate のみ)、core は Phase C-D で genuine discharge。honesty 4 条件 ((a) 型 ≠ 結論、(b) docstring NOT load-bearing 明示、(c) Phase C-D で discharge、(d) `@audit:staged(continuous-aep-gaussian)`) 全て遵守。

### #2 (2026-05-24) Phase 0 完了、codebook 測度 = Option A (2 段 `Measure.pi`)

Axis 1 inventory ([`...-axis1-codebook.md`](awgn-achievability-typicality-mathlib-inventory-axis1-codebook.md))、6 サブ項目 100% Mathlib 既存。採用形 `Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σ²))`。理由: `AwgnCode.encoder` と defeq / `iIndepFun_pi` (Basic.lean:784) + `measurePreserving_eval` (Pi.lean:407) で 2-3 行 / T-1 不発動。

- **trap 1**: `iIndepFun_pi` の `[∀ i, IsProbabilityMeasure (μ i)]` がファイル変数継承で signature に現れない → prob measure 維持必須
- **trap 2**: `pi_map_eval` (Pi.lean:379) は scalar `(∏ μ j univ) • μ i` 付き → 必ず `measurePreserving_eval` (line 407, prob 専用) 選択

### #3 (2026-05-24) Phase 0 完了、typical set 定義形 = Option γ (`klDiv` 形)

Axis 3 inventory ([`...-axis3-density.md`](awgn-achievability-typicality-mathlib-inventory-axis3-density.md))、3 形比較:

- α (`rnDeriv` 形): `Measure.pi × Measure.rnDeriv` loogle 0 declarations → bridge 50-100 行、却下
- β (`differentialEntropy` 形): 既存 `jointDifferentialEntropyPi_le_sum` の `h_llr_split` 負債継承 → 却下
- γ (`klDiv` 形): Mathlib `klDiv_compProd_eq_add` (無条件等号) + 既存 `klDiv_pi_eq_sum` / `klDiv_gaussianReal_gaussianReal_eq` で完全乗算、負債断絶 → **採用**

`multivariateGaussian` の `PosSemidef` 要件は T-2 採用で回避。

### #4 (2026-05-24) Phase A + B-0 完了、`gaussianCodebook` + `IsContinuousAEPGaussian` 確定

`AWGNAchievabilityDischarge.lean` (~270 行) Phase A 本体 + B-0 predicate + Phase C/D/E skeleton sorry で publish。判断 #2 採用形そのまま (識別子は `σsq`、Lean 4 は `²` を identifier に含まない)。Mathlib lemma 確定:

- A-2: `infer_instance` 1 行
- A-3: `MeasureTheory.measurePreserving_eval` (Pi.lean:407、trap 2 厳守)
- A-4: `iIndepFun_pi` (Basic.lean:784、trap 1 厳守) + `iIndepFun.indepFun`

Phase B-0 predicate (Option γ `klDiv` 形): 3 conjunct ((i) joint codebook+noise prob ≥ 1−ε / (ii) typical-set volume bound vs Lebesgue / (iii) indep-pair upper bound vs prod marginal)、`P : ℝ` + `N : ℝ≥0` のみで quantify。honesty 4 条件 ((a) 型 ≠ 結論 / (b) NOT load-bearing 明示 + Mathlib gap 明記 / (c) Phase C-D で union bound + expurgation 本物 discharge / (d) `@audit:staged(continuous-aep-gaussian)`) 遵守。検証 silent、9 placeholder sorry。

**任意 pivot 案** (Phase C 着手前): bound (ii) を `differentialEntropy_gaussianReal` の closed form `(1/2) log (2πe(P+N))` 書換、ただし Option β 負債継承リスク → Phase C-D 着手時再評価。

### #5 (TBD) Phase B 完了時、`IsContinuousAEPGaussian` predicate 確定形

T-2 採用方針確定済 (判断 #1)、Phase B 着手時に Option γ (`klDiv` 形) に整合する predicate 具体形を確定 + audit:staged タグ付与確認 append 予定 → #4 で実質完了。

### #7 (2026-05-24) E-1 staged hyp `IsAwgnPowerConstraintRealizable` に false-statement defect → bundle pivot 完了

Phase E-1 で導入した `IsAwgnPowerConstraintRealizable P N` (判断 #6) が **false-statement defect** 発覚。原因: `Xᵢ ~ N(0, P)` i.i.d. の chi-square mass `P(∑Xᵢ² ≤ nP) ≥ 1−ε` は CLT で `→ 0.5⁺`、`Fin M` 結合で `(0.5+o(1))^M`、unsatisfiable。標準解 (Cover-Thomas 9.2): codebook variance を `P' < P` に下げる → SLLN で `P(∑Xᵢ² ≤ nP) → 1`。

**Pivot** (sibling [`awgn-power-constraint-realizable-pivot-plan.md`]、Option C bundled):

- 3 staged hyp (`h_aep` + `h_rand` + `h_power`) を 1 bundle `IsAwgnRandomCodingFeasible P N h_meas` に統合、bundle が `∃ P' ∈ (0, P]` witness を共有
- 新規 predicate 2 件 (`9dcef00`): `IsAwgnPowerConstraintHonest (P_cb P_target N)` (生成/制約分離) + `IsAwgnRandomCodingFeasible (P N h_meas)` (`∀ R, ∃ P' ∈ (0, P], rate-margin + AEP + RC-integral + PowerConstraintHonest` bundle)
- 旧 `IsAwgnPowerConstraintRealizable` orphan 化、`@audit:defect(false-statement)` + body 不変で残置
- Phase 3 (`2ace40b`): consumer 1641 行 / 0 sorry / silent 復元、`gaussianCodebook P → P'` 15 箇所 sed + rate-bound P→P' bridge 20 行 (`Real.log_le_log`)
- 独立 honesty audit pass、4 条件遵守、name laundering なし
- 完了 (`4fdf403`、`@audit:suspect(awgn-power-constraint-realizable-pivot)` closure)

**Soft caveat**: bundle の `P' ≤ P` (non-strict) は `P' = P` 退化を許容、その場合 v1 unsatisfiable form 復活。Phase 3 body は形式的に通る (defect ではない) が、genuine discharger で `P' < P` 必須。

**E-1 staged 総数**: 3 hyp → 1 bundle hyp、analytic 3 gap (continuous SMB / n-d differentialEntropy / chi-square SLLN) 不変。

proof-log: `proof-log-awgn-power-constraint-realizable-pivot-phase{2,3}.md`、詳細は sibling plan #1-#3。

### #6 (2026-05-24) Phase D 完了 + Phase E signature refine、E-1 body は次セッションへ defer

`AWGNAchievabilityDischarge.lean` (716 行)、Phase D 0 sorry + E-2/E-3 1 行 wrapper、**E-1 body のみ sorry 1 個残置**。

**Phase D 確定**:

- D-1 `awgn_exists_codebook_le_avg`: `MeasureTheory.exists_le_lintegral` (Average.lean:738) 直接 + `le_trans`、B 抽象化
- D-2 `awgn_expurgate_worst_half`: pure `Finset` arithmetic ~40 行 (`card_filter_add_card_filter_not` + `sum_lt_sum_of_nonempty` + `nlinarith`)、`Nat → ℝ` cast plumbing で +25 行
- D-3 `awgn_extract_AwgnCode`: `AwgnCode` constructor + decoder + `4ε → 5ε` slack、`h_power` / `h_max_Pe` 仮定

**追加 staged hyp** `IsAwgnPowerConstraintRealizable P N` (4 条件遵守、後に #7 で defect 発覚 → bundle pivot): 型 = `∀ ε R, ... gaussianCodebook M n P.toNNReal {c | ∀ m, ∑(c m i)² ≤ n*P} ≥ 1−ε`。E-1 staged 3 本 (h_aep + h_rand + h_power) — 各 hyp は独立 analytic 壁 (連続 AEP / RC integral / power SLLN)。

**E-2/E-3**: 1 行 wrapper、残 hyp = staged 3 + h_mi_bridge + h_converse 計 5。

**E-1 body 残置 1 sorry**: skeleton 7 ステップ (ε scaling → max N₀ → M=2⌈exp(nR)⌉ → AEP → per-m bound + power-OK → Fubini で ∫⁻ ∑_m Pe ≤ M·2ε → `awgn_exists_codebook_le_avg` 抽出 → `awgn_expurgate_worst_half` → `Finset.equivFin` reindex → `awgn_extract_AwgnCode` + ε scaling)。~100-200 行、当 session 時間枠不足で defer。

**rebrand 回避**: `IsAwgnExpurgationFeasible` 案は D-1/D-2 を hyp 化、name laundering 抵触 → 却下。E-1 body は inline で honest discharge。`@audit:residual(awgn-typicality-E1-body)` タグ。

検証 silent / warning 1 (sorry at line 670)。次 session: E-1 body inline + `Finset.equivFin` reindex + Phase V (`InformationTheory.lean` 編入 + re-audit) + 進捗 ✅ 更新 → #7 経由で完走済。
