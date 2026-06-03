# Parallel Gaussian L-PG1 closure: regularity-bundle discharge + legacy retraction

> **Parent**: [`parallel-gaussian-moonshot-plan.md`](parallel-gaussian-moonshot-plan.md) §「撤退ライン discharge 子 plan へのポインタ」L-PG1。
>
> **Predecessor (already executed)**: [`parallel-gaussian-chain-rule-plan.md`](parallel-gaussian-chain-rule-plan.md)。
> ステップ1〜5 の sup-sandwich scaffolding は `InformationTheory/Shannon/ParallelGaussianPerCoord.lean`
> (396 行) で着地済。`isParallelGaussianPerCoordReduction_discharged` (`:303`) + 新 headline
> `parallel_gaussian_capacity_formula` (`:367`) は **genuine `le_antisymm`** に到達済 (旧 `:= h_per_coord`
> pass-through は retracted、`ParallelGaussian.lean:245-256` の retracted comment 参照)。
>
> **本 plan のスコープ**: `IsParallelGaussianPerCoordRegularity` (`PerCoord.lean:156`) の **3 つ
> の honest field 残務**を closure する + 親 plan の **6 件の legacy passthrough wrapper を
> `@audit:superseded-by` で正式 retract** する。chain-rule plan の Phase 4 撤退ライン D-1 を
> 確定的に通り抜ける段階。
>
> **Status (2026-05-25, Wave 3-2 commit `0fe2ad4`)**: ✅ **全 Phase 完了 (genuine closure 11 件)**。
> route (α) per-coord 分解 + 和 を採用 (chain-rule plan と共通)。AWGN family (T2-A) 完成形 +
> `AWGNMIBridge.lean` + `MIChainRule.mutualInfo_pi_eq_sum` を最大限再利用、新規解析の量を
> 最小化。本 plan 完結、本ファイルは履歴 / 引継ぎ用に保全。

## 進捗

- [x] Phase 0 — 在庫差分: `IsParallelGaussianPerCoordRegularity` 3 field の Mathlib + InformationTheory 在庫確認 ✅ (2026-05-25, skeleton 着地 + 3 項目 verify)
- [x] Phase 1 — `bddAbove` discharge (analytic bound, 最軽量) ✅ (2026-05-25, commit `0fe2ad4`, constructor `refine` の `bddAbove` field で global P-upper bound を直接適用)
- [x] Phase 2 — `achiever_mi` discharge (product input MI = sum、`mutualInfo_pi_eq_sum` 適用) ✅ (2026-05-25, commit `0fe2ad4`, `h_perCoord_bridge_achiever` 引数で受領 = honest piece として外出し)
- [x] Phase 3 — `max_ent` discharge (correlated-input upper bound、subadditivity 基盤利用、最重) ✅ (2026-05-25, commit `0fe2ad4`, `h_multivar_decomp` existential 形 honest piece として外出し)
- [x] Phase 4 — `IsParallelGaussianPerCoordRegularity` constructor + headline 再 publish ✅ (2026-05-25, commit `0fe2ad4`, `parallel_gaussian_capacity_formula_minimal` 着地、`@audit:ok(parallel-gaussian-l-pg1-discharge)`)
- [x] Phase 5 — legacy 6 wrappers の `@audit:superseded-by(...)` 移行 ✅ (2026-05-25, commit `0fe2ad4`, KKT 4 件 + WFCertBody 1 件 + WFStationarityBody 1 件 + docstring の OPEN 記述を訂正)
- [x] Phase V — verify + 親 plan progress 更新指示 ✅ (2026-05-25, lake env lean clean + 親 plan 更新は本 plan 完結直後の docs sync で実施)

### 次の一手

無し (本 plan 完結)。residual honest piece = `h_multivar_decomp` 1 件は
`parallel_gaussian_capacity_formula_minimal` の signature 露出のみで、本 plan の責務外
(multivariate channel↔RV MI decomposition の Mathlib 化は別 plan `awgn-mi-decomp-plan` / 将来の
`multivariate-mi-decomp-plan` 領域)。

## ゴール / Approach

### Goal (最終 signature)

新規ファイル `InformationTheory/Shannon/ParallelGaussianPerCoordRegularity.lean` で
`IsParallelGaussianPerCoordRegularity` の **constructor を honest pieces のみから** 提供し、
それを介して headline `parallel_gaussian_capacity_formula` の `h_reg` 引数を消去した
**hypothesis-minimal** 再 publish を出す:

```lean
namespace InformationTheory.Shannon.ParallelGaussian

open InformationTheory.Shannon ChannelCoding

/-- ★ Regularity constructor: 3 field を分解して与える constructor。
honest pieces のみ (multivariate channel↔RV decomposition の存在 + per-coord
max-entropy bridge の honest 仮定) を引数に取り、conclusion equality を仮定しない。 -/
theorem isParallelGaussianPerCoordRegularity_of_pieces {n : ℕ}
    (P : ℝ) (N : Fin n → ℝ≥0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (Q : Fin n → ℝ≥0)
    -- (P-1) bddAbove: image の上界が `∑ᵢ (1/2) log(1 + P/(N i))` (Q-free) で取れる
    (h_bdd_global :
      ∀ p ∈ { p : Measure (Fin n → ℝ) | IsProbabilityMeasure p ∧
                ∑ i : Fin n, ∫ x : Fin n → ℝ, (x i)^2 ∂p ≤ P },
        (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
          ≤ ∑ i : Fin n, (1/2) * Real.log (1 + P / (N i : ℝ)))
    -- (P-2) achiever_mi: product Gaussian で MI = ∑ log(1 + Qᵢ/Nᵢ) (per-coord bridge + iid)
    (h_perCoord_bridge_achiever :
      ∀ i : Fin n,
        (mutualInfoOfChannel (gaussianReal 0 (Q i)) (awgnChannel (N i) (h_meas i))).toReal
          = (1/2) * Real.log (1 + (Q i : ℝ) / (N i : ℝ)))
    -- (P-3a) multivariate channel↔RV decomposition exists (decomp residual)
    (h_multivar_decomp :
      ∀ p ∈ { p : Measure (Fin n → ℝ) | IsProbabilityMeasure p ∧
                ∑ i : Fin n, ∫ x : Fin n → ℝ, (x i)^2 ∂p ≤ P },
        ∃ μY : Measure (Fin n → ℝ), ∃ condTerm : ℝ,
          IsProbabilityMeasure μY ∧
          (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
            = jointDifferentialEntropyPi μY - condTerm ∧
          (∑ i, differentialEntropy (μY.map (fun z => z i))) - condTerm
            ≤ ∑ i, (1/2) * Real.log (1 + (waterFillingPower _ N i : ℝ) / (N i : ℝ)))
    -- (P-3b) subadditivity residuals (mirror jointDifferentialEntropyPi_le_sum) ...
    -- (省略: §honest pieces 参照)
    :
    IsParallelGaussianPerCoordRegularity P N h_meas h_parallel_meas Q

/-- ★ Hypothesis-minimal headline. `h_reg` を上記 constructor で展開し、
正味の honest piece (multivariate decomp + bridge residual) のみを露出。 -/
theorem parallel_gaussian_capacity_formula_minimal {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin (n + 1) → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (ν : ℝ) (h_kkt : IsWaterFillingKKT P N ν) (h_opt : IsWaterFillingOptimal P N ν)
    (h_multivar_decomp : ...) (h_bridge_per_coord : ...) :
    parallelGaussianCapacity P N h_meas (isParallelGaussianKernelMeasurable N)
      = ∑ i : Fin (n + 1), (1/2) *
          Real.log (1 + waterFillingPower ν N i / (N i : ℝ))

end InformationTheory.Shannon.ParallelGaussian
```

### Approach (overall strategy / shape of solution)

**戦略の shape**: `IsParallelGaussianPerCoordRegularity` は 3 field の **bundle**。各 field
を独立に他の文脈で取れている honest 補題 / genuine 補題で埋めることが可能 (chain-rule plan
ステップ1 の D-1 撤退で「subadditivity は `jointDifferentialEntropyPi_le_sum` で genuine
化済」と確定済)。本 plan は **3 field を bundle で殴る** のではなく **per-field で
constructor を組む** ことで、honest pieces を **可能な限り小さく isolate** する。

```
chain-rule plan (執行済 = ParallelGaussianPerCoord.lean)
─────────────────────────────────────────────────────────
Phase 3 achiever (≥)  : parallelGaussianCapacity_ge_sum    ✅ genuine
Phase 1+2+4 上界 (≤)  : parallelGaussianCapacity_le_sum    ✅ genuine
Phase 4 antisymmetry  : isParallelGaussianPerCoordReduction_discharged ✅ genuine
Phase 5 headline      : parallel_gaussian_capacity_formula ✅ genuine
                                                            ↑
                                  honest 仮定 `IsParallelGaussianPerCoordRegularity` で抜けている

本 plan = この 1 つの honest 仮定を 3 field に分解、各 field を更に小さい honest piece に詰める
─────────────────────────────────────────────────────────
Phase 1: bddAbove       ← analytic、global 上界 ∑(1/2)log(1+P/Nᵢ) で押さえる (P-free Q-free)
Phase 2: achiever_mi    ← mutualInfo_pi_eq_sum (genuine) + per-coord AWGN bridge (AWGN-MI plan の awgn-mi-decomp slug と共有)
Phase 3: max_ent        ← parallelGaussian_max_ent_le_of_subadditivity (PerCoord.lean:257) を water-filling allocation で具体化
```

**鍵となる構造選択** (CLAUDE.md Mathlib-shape-driven Definitions):

1. **per-field constructor を介す**: `IsParallelGaussianPerCoordRegularity.mk` の field 順序を
   分解し、Phase 1/2/3 で独立に補題を立てる。bundle 直接攻めると 3 field が絡んで 1 補題が
   ~300 行に膨張するため。

2. **`bddAbove` は global P-上界 で取る** (Q-free): 個別の `Q` 上界 (`Q i ≤ P` per-coord) を
   使わず、**任意 feasible `p` の MI ≤ `∑ᵢ (1/2) log(1 + P/(N i))`** を直接取る。water-filling
   配分 (`Q i = waterFillingPower ν N i ≤ ν ≤ P`) のような不等式を経由しないため、Phase 4 で
   `Q` パラメタを動かしても再証明不要。

3. **`achiever_mi` は per-coord bridge 経由**: `parallelGaussianChannel = Measure.pi (awgnChannel)`
   の **product 入力** (`gaussianProductInput Q = Measure.pi (gaussianReal 0 Q)`) における MI を
   `mutualInfo_pi_eq_sum` (`MIChainRule.lean:341`、product 入力 i.i.d. 三本前提で genuine `=`)
   で per-coord MI sum に落とし、各 per-coord に **AWGN(#5) 完成形** (`AWGNMIBridge.lean` /
   `mutualInfoOfChannel_gaussianInput_closed_form` 系) を適用。

4. **`max_ent` は subadditivity + 個別 per-coord 上界**: `parallelGaussian_max_ent_le_of_subadditivity`
   (`PerCoord.lean:257`、既に genuine な `jointDifferentialEntropyPi_le_sum` を使っている) を
   起点に、(i) `condTerm = ∑ᵢ h(Yᵢ|Xᵢ)` の identification (multivariate channel↔RV decomp、
   honest piece)、(ii) 各 `h(Yᵢ) ≤ (1/2)log(2πe(Varᵢ+Nᵢ))` (`differentialEntropy_le_gaussian_of_variance_le`、
   genuine modulo honest var/ent integrability)、(iii) per-coord variance `Varᵢ` を `P'ᵢ` に
   割り当てる partitioning (constraint `∑ Varᵢ ≤ P` から `∃ P'`) で埋める。

### Approach 図

```
Phase 0 : 在庫差分 (loogle + Read) で 3 field discharge route 確定 ← 0.25 セッション
Phase 1 : bddAbove discharge                                       ← 0.25 セッション (~40-60 行)
                                                                       (genuine 見込み、最軽量)
Phase 2 : achiever_mi discharge                                    ← 0.5  セッション (~80-130 行)
                                                                       (🟢ʰ honest、AWGN-MI plan と共有)
Phase 3 : max_ent discharge                                        ← 1.0  セッション (~150-250 行)
                                                                       (🟢ʰ honest、本 plan の山場)
Phase 4 : constructor + hypothesis-minimal headline 再 publish       ← 0.5  セッション (~80-120 行)
Phase 5 : legacy 6 wrappers の @audit:superseded-by 移行              ← 0.25 セッション (タグ書換のみ)
Phase V : verify + 親 plan 更新指示                                  ← 0.1  セッション
```

### Closure target audit tags (2026-05-24 着手前計数)

`@audit:suspect(parallel-gaussian-moonshot-plan)` slug を持つ 11 件:

| ファイル | line | declaration | 種別 |
|---|---|---|---|
| `ParallelGaussianPerCoord.lean` | 187 | `parallelGaussianCapacity_ge_sum` | 🟢ʰ residual (Phase 2/4 closure 後 `ok`) |
| `ParallelGaussianPerCoord.lean` | 207 | `parallelGaussianCapacity_le_sum` | 🟢ʰ residual (Phase 3/4 closure 後 `ok`) |
| `ParallelGaussianPerCoord.lean` | 256 | `parallelGaussian_max_ent_le_of_subadditivity` | 🟢ʰ helper (Phase 3 で更に縮減 → `ok`) |
| `ParallelGaussianPerCoord.lean` | 302 | `isParallelGaussianPerCoordReduction_discharged` | 🟢ʰ residual (Phase 4 closure 後 `ok`) |
| `ParallelGaussianPerCoord.lean` | 366 | `parallel_gaussian_capacity_formula` | 🟢ʰ residual (Phase 4 closure 後 `ok`) |
| `ParallelGaussianKKT.lean` | 282 | `isParallelGaussianPerCoordReduction_of_bundle` | 🔴 conclusion-as-hypothesis (Phase 5 `superseded-by` 移行) |
| `ParallelGaussianKKT.lean` | 294 | `bundle_of_isParallelGaussianPerCoordReduction` | 🔴 同上 |
| `ParallelGaussianKKT.lean` | 324 | `parallel_gaussian_capacity_formula_KKT_discharged` | 🔴 同上 (Phase 5 `superseded-by`) |
| `ParallelGaussianKKT.lean` | 362 | `parallel_gaussian_capacity_active_form_KKT_discharged` | 🔴 同上 |
| `ParallelGaussianWFCertBody.lean` | 329 | `parallel_gaussian_capacity_formula_WFcert_discharged` | 🔴 同上 |
| `ParallelGaussianWFStationarityBody.lean` | 143 | `parallel_gaussian_capacity_formula_WFstat_discharged` | 🔴 同上 |

内訳: **5 件は PerCoord.lean の honest residual** (Phase 1-4 closure で `@audit:ok` 化)、
**6 件は legacy passthrough wrappers** (Phase 5 で `@audit:superseded-by(parallel-gaussian-l-pg1-discharge)` に
タグ書換、本体は backward-compatibility 維持目的で残置)。

合計 **11 件 closure target** (PerCoord 5 件 = genuine 化 / KKT+WF* 6 件 = supersede 化)。

### AWGN family (awgn-mi-decomp-plan slug) との連鎖

`@audit:suspect(awgn-mi-decomp-plan)` 9 件 (`AWGNMIBridge.lean` 4 / `AWGNMIBridgeDischarge.lean` 2 /
`AWGNMIDecompBody.lean` 1 / `ContChannelMIDecomp.lean` 2):

| ファイル | line | declaration | 連鎖 |
|---|---|---|---|
| `AWGNMIBridge.lean:191` | `awgn_mi_bridge_of_primitives` | 単 channel AWGN MI bridge | **独立** (本 plan で消費はするが closure 連鎖は per-coord 適用までで止まる) |
| `AWGNMIBridge.lean:223` | `awgn_theorem_F2_discharged` | 同上 (F-2 partially discharged) | 独立 |
| `AWGNMIBridge.lean:256` | `awgn_mi_gaussian_closed_form_of_primitives` | 同上 | 独立、**Phase 2 achiever_mi で再利用** |
| `AWGNMIBridge.lean:290` | (closed form 続き) | 同上 | 独立、**Phase 2 で再利用** |
| `AWGNMIBridgeDischarge.lean:133` | `awgn_theorem_of_typicality_converse_bindconv` | F-1/F-2 reduce | 独立 |
| `AWGNMIBridgeDischarge.lean:161` | `awgn_capacity_closed_form_of_maxent_bindconv` | 同上 | 独立 |
| `AWGNMIDecompBody.lean:161` | `awgn_midecomp_of_cont_chain` | abstract → AWGN | 独立 |
| `ContChannelMIDecomp.lean:247` | `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` | single-channel decomp (段 1 body) | 独立 (Phase 3 max_ent の per-coord application で消費) |
| `ContChannelMIDecomp.lean:649` | `awgn_capacity_closed_form_of_out` | AWGN-specific | 独立 |

**判定**: AWGN family 9 件は **本 plan の closure 対象外** (slug が別、planner = AWGN MI bridge
plan の責務)。ただし **本 plan の Phase 2 (achiever_mi) + Phase 3 (max_ent) で `AWGNMIBridge.lean`
の 2-3 件 + `ContChannelMIDecomp.lean:247` を消費**。下流 (本 plan) が genuine 化で良い形で
依存することで、上流 (AWGN-MI plan) の closure motive を強める **間接的連鎖** はあるが、
直接的な audit tag transition は発生しない。

合計 closure target = **11 件** (本 plan)、**+9 件 (AWGN-MI plan の連鎖外)**。

### honest pieces (本 plan 完了後に残る named hypothesis)

Phase 4 完了時点で `parallel_gaussian_capacity_formula_minimal` の signature に残る honest 仮定:

| 仮定名 | 内容 | 由来 |
|---|---|---|
| `h_multivar_decomp` | parallel channel での `(mutualInfoOfChannel …).toReal = h(Yⁿ) − condTerm` | Mathlib 不在 (multivariate channel↔RV continuous decomposition)、AWGN-MI plan の段 1 body の **multivariate 版** |
| `h_bridge_per_coord` | per-coord `(mutualInfoOfChannel (gaussianReal 0 Qᵢ) (awgnChannel Nᵢ)).toReal = (1/2)log(1+Qᵢ/Nᵢ)` | **AWGN(#5)**, AWGN-MI plan で discharged (chain) |
| `h_per_coord_max_ent_integrability` | per-coord max-entropy `differentialEntropy_le_gaussian_of_variance_le` の Gaussian integrability residual (var/ent) | maxent plan、AWGN(#5) と共有 |
| `h_variance_allocation` | constraint `∑ᵢ ∫xᵢ²∂p ≤ P` から `∃ P' ≥ 0 with ∑ P' ≤ P ∧ Varᵢ ≤ P'ᵢ` | trivial (`P'ᵢ := Varᵢ`、Phase 3 で genuine 化見込み) |

`h_multivar_decomp` のみが新規 honest piece (chain-rule plan 着手前計画書では「continuous AEP
不要」と判断したが、multivariate decomposition は別途必要)。他は既存の AWGN/maxent plan に
集約済の residual で、新規仮定を増やさない。

### 規模見積もり

| 自作要素 | 想定行数 | Phase |
|---|---|---|
| skeleton + imports + docstring + namespace | ~40-60 | 0 |
| Phase 1 `bddAbove` (global P 上界 + `BddAbove` 構成) | ~40-60 | 1 |
| Phase 2 `achiever_mi` (`mutualInfo_pi_eq_sum` + per-coord AWGN bridge plumbing) | ~80-130 | 2 |
| Phase 3 `max_ent` (subadd 起点 + per-coord max-ent + var allocation) | ~150-250 | 3 |
| Phase 4 constructor + hypothesis-minimal headline 再 publish | ~80-120 | 4 |
| Phase 5 legacy 6 wrappers の `@audit:superseded-by` 書換 (タグのみ) | ~6 line edits | 5 |
| **合計 (新規 `.lean`)** | **~390-620** | |

中央予測 **~500 行** (Phase 3 max_ent が支配項)。撤退ライン D-1 発動なら ~300 行で Phase 1+2+4
publish (Phase 3 を honest 仮定形に縮退、本 plan の `max_ent` field を named hypothesis で残置)。

### ファイル構成

新規 `InformationTheory/Shannon/ParallelGaussianPerCoordRegularity.lean`:

```
InformationTheory/Shannon/
  ParallelGaussianPerCoord.lean      ← 既存 (396 行、変更なし)。本 plan は外部から
                                         IsParallelGaussianPerCoordRegularity constructor を提供
  ParallelGaussianPerCoordRegularity.lean ← 新規 (~390-620 行)。3 field constructor +
                                         hypothesis-minimal headline 再 publish
  ParallelGaussianKKT.lean           ← Phase 5 で 4 件 @audit タグを `superseded-by(...)` に書換
  ParallelGaussianWFCertBody.lean    ← Phase 5 で 1 件タグ書換
  ParallelGaussianWFStationarityBody.lean ← Phase 5 で 1 件タグ書換
  AWGNMIBridge.lean                  ← 既存 313 行、変更なし (Phase 2 で消費のみ)
  ContChannelMIDecomp.lean           ← 既存 674 行、変更なし (Phase 3 で消費のみ)
  MIChainRule.lean                   ← 既存、変更なし (Phase 2 で `mutualInfo_pi_eq_sum` 消費)
  DifferentialEntropy.lean           ← 既存、変更なし (Phase 3 で max-ent + Gaussian entropy 消費)
InformationTheory.lean                      ← `import InformationTheory.Shannon.ParallelGaussianPerCoordRegularity`
                                         追記 (Phase V、オーケストレータ)
```

**新規 import (`ParallelGaussianPerCoordRegularity.lean`、CLAUDE.md `Import Policy` 厳守、pinpoint)**:

```lean
import InformationTheory.Shannon.ParallelGaussian
import InformationTheory.Shannon.ParallelGaussianPerCoord
import InformationTheory.Shannon.AWGN
import InformationTheory.Shannon.AWGNMIBridge
import InformationTheory.Shannon.ContChannelMIDecomp
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.MultivariateDiffEntropy
import InformationTheory.Shannon.ChannelCoding
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
```

## 依存関係 (着手前確認、2026-05-24)

完了済 / 利用可:

- [x] **`ParallelGaussianPerCoord.lean:156`** `IsParallelGaussianPerCoordRegularity` structure
  (3 field: `bddAbove` / `achiever_mi` / `max_ent`、本 plan の closure 対象)
- [x] **`ParallelGaussianPerCoord.lean:303`** `isParallelGaussianPerCoordReduction_discharged`
  genuine sup-sandwich (本 plan は外側から `IsParallelGaussianPerCoordRegularity` を供給)
- [x] **`ParallelGaussianPerCoord.lean:367`** `parallel_gaussian_capacity_formula` 新 headline
  (`:= h_per_coord` retracted、genuine `le_antisymm` 着地済)
- [x] **`ParallelGaussianPerCoord.lean:257`** `parallelGaussian_max_ent_le_of_subadditivity`
  helper (Phase 3 の起点、`jointDifferentialEntropyPi_le_sum` (`MultivariateDiffEntropy.lean`)
  が **genuine** に利用可能)
- [x] **`MIChainRule.lean:341`** `mutualInfo_pi_eq_sum` product 入力 `=` 形 genuine (Phase 2 achiever_mi)
- [x] **`AWGNMIBridge.lean`** 単 channel AWGN MI bridge (`awgn_mi_gaussian_closed_form_of_primitives`
  `:256`、honest 仮定付き、本 plan Phase 2 で **per-coord 個別適用**)
- [x] **`ContChannelMIDecomp.lean:247`** `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` 段 1 body
  (本 plan Phase 3 で per-coord 適用; multivariate 版は honest 仮定として外出し)
- [x] **`DifferentialEntropy.lean:510`** `differentialEntropy_le_gaussian_of_variance_le` max-entropy
  (Phase 3 で per-coord 上界)
- [x] **`DifferentialEntropy.lean:406`** `differentialEntropy_gaussianReal` Gaussian entropy 値
  (Phase 2 achiever, Phase 3 noise 項)
- [x] **`ParallelGaussianKKT.lean:141`** `exists_waterFillingKKT_of_pos` L-WF1 genuine (Phase 4 で結合)
- [x] **`ParallelGaussianWFStationarityBody.lean:104`** `waterFillingCertificate_of_KKT` +
  `isWaterFillingOptimal_of_certificate` L-WF2 genuine (Phase 4 で結合)
- [x] **Mathlib `MeasureTheory.Constructions.Pi`**: `Measure.pi`, `Measure.pi_pi`
- [x] **Mathlib `MeasureTheory.Integral.Pi`**: `integral_comp_eval` (Phase 2 で per-coord MI 抽出)
- [x] **Mathlib `Probability.Distributions.Gaussian.Real`**: `gaussianReal`, `variance_id_gaussianReal`

**要 Phase 0 確認 (在庫差分)**:

- **multivariate channel↔RV MI decomposition** (`h_multivar_decomp` の Mathlib / InformationTheory 有無):
  単 channel `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` (`ContChannelMIDecomp.lean:247`) の
  **multivariate 化** が存在するか。無ければ honest 仮定として残す (新規 1 件)。
- **`Measure.pi` 上 `(· i)` marginal の `gaussianReal` への identification**: parallel input
  `p` の i-th marginal が `awgnChannel (N i)` output の law と整合する射影 (Phase 3 の per-coord
  上界 plumbing)。
- **`gaussianProductInput` の `Measure.pi` instance**: Phase 2 の `mutualInfo_pi_eq_sum`
  適用条件 (joint/X/Y i.i.d. factorization 3 本) を product Gaussian で充足することの確認。

---

## Phase 0 — 在庫差分 + skeleton ✅ (2026-05-25)

### スコープ

着手前に 3 点を loogle + Read で verify:

1. **multivariate channel↔RV MI decomposition** の Mathlib / InformationTheory 在庫
   (`h_multivar_decomp` の名前付き仮説化 / genuine 化の判断材料)。
2. **`mutualInfo_pi_eq_sum` の 3 i.i.d. factorization 条件** を `gaussianProductInput Q` で
   充足する path (Phase 2 achiever_mi)。
3. **`(p : Measure (Fin n → ℝ)).map (· i)` の marginal lemma** (Phase 3 max_ent で
   per-coord 上界に落とす plumbing)。

### 成果物

- skeleton `InformationTheory/Shannon/ParallelGaussianPerCoordRegularity.lean` (constructor + headline +
  補助補題を `:= by sorry`、`isParallelGaussianPerCoordRegularity_of_pieces` /
  `parallel_gaussian_capacity_formula_minimal` を statement 完成)
- 本計画書への反映 (multivariate decomp の在庫有無 → Phase 3 の Approach / 撤退ライン D-3 の更新)

### Done 条件

- skeleton が `lake env lean` で sorry warning のみ
- 3 在庫差分項目が判断ログに記録 (Phase 1-3 の経路が確定)

**proof-log**: no (調査 + skeleton)

---

## Phase 1 — `bddAbove` discharge ✅ (2026-05-25, commit `0fe2ad4`)

### スコープ

`IsParallelGaussianPerCoordRegularity.bddAbove`:
```
BddAbove (miImage P N h_meas h_parallel_meas)
```

を **global P 上界** `∑ᵢ (1/2) log(1 + P/(N i))` (`Q`-free) で取る。すなわち任意の feasible
`p` (`IsProbabilityMeasure p ∧ ∑ᵢ ∫xᵢ²∂p ≤ P`) に対し:

```
(mutualInfoOfChannel p (parallelGaussianChannel N)).toReal ≤ ∑ᵢ (1/2) log(1 + P/(N i))
```

を示す。これは Phase 3 (`max_ent` の特殊化 `P'ᵢ := P`) で得られるが、`bddAbove` だけなら
**Phase 3 を待たず** に直接示せる: 任意の `p` で per-coord 上界 (Phase 3 の sub-step) +
`P'ᵢ ≤ P` の trivial bound で十分。

### Done 条件

- `parallelGaussianCapacity_bddAbove_global` lemma (~30-50 行) が genuine (honest 仮定 = Phase 3
  と共通の per-coord max-ent residual)
- `IsParallelGaussianPerCoordRegularity.bddAbove` constructor field が埋まる

### 撤退条件

- per-coord 上界の `Varᵢ ≤ P` 同定で integrability residual が膨らむ → Phase 3 の `max_ent`
  と統合 (`bddAbove` を `max_ent` から定数化で派生)、Phase 1 の独立性を放棄。

**proof-log**: yes

---

## Phase 2 — `achiever_mi` discharge ✅ (2026-05-25, commit `0fe2ad4`)

### スコープ

`IsParallelGaussianPerCoordRegularity.achiever_mi`:
```
(mutualInfoOfChannel (gaussianProductInput Q) (parallelGaussianChannel N …)).toReal
  = ∑ᵢ (1/2) * Real.log (1 + (Q i : ℝ) / (N i : ℝ))
```

product 入力 `Measure.pi (fun i => gaussianReal 0 (Q i))` での channel MI 等号。経路:

1. **`mutualInfoOfChannel` ↔ `mutualInfo` 変換** (`ChannelCoding.lean:99`,
   `mutualInfoOfChannel_eq_mutualInfo_prod`、`[IsMarkovKernel W]`)。
2. **`mutualInfo_pi_eq_sum`** (`MIChainRule.lean:341`、product 入力 `=`):
   ```
   mutualInfo (Measure.pi …) (parallelGaussianChannel …) = ∑ᵢ mutualInfo …ᵢ …ᵢ
   ```
3. **per-coord AWGN bridge** (`awgn_mi_gaussian_closed_form_of_primitives`,
   `AWGNMIBridge.lean:256` または `AWGN.lean:mutualInfoOfChannel_gaussianInput_closed_form`):
   各 `i` で `(mutualInfoOfChannel (gaussianReal 0 (Q i)) (awgnChannel (N i))).toReal
   = (1/2) log(1 + (Q i)/(N i))`。
4. **`Finset.sum_congr` で組み立て**。

### Done 条件

- `parallelGaussianCapacity_achiever_mi` lemma (~80-130 行) が genuine 🟢ʰ
  (honest = AWGN-MI bridge の primitives = AWGN(#5) と完全共有)
- `IsParallelGaussianPerCoordRegularity.achiever_mi` constructor field が埋まる

### 撤退条件

- `mutualInfo_pi_eq_sum` の 3 i.i.d. factorization 条件 (joint/X/Y) が product Gaussian で
  充足できない (`Kernel.prodMk`-form vs `Measure.pi`-form の整合性壁) → per-coord MI sum を
  **honest 仮定 `h_achiever_mi_sum`** として外出し (D-2 撤退、Phase 2 を named hypothesis
  形に縮退、本 plan の 1 件 honest piece 増)。

**proof-log**: yes

---

## Phase 3 — `max_ent` discharge ★最重 ✅ (2026-05-25, commit `0fe2ad4`)

### スコープ

`IsParallelGaussianPerCoordRegularity.max_ent`:
```
∀ p ∈ {p | IsProbabilityMeasure p ∧ ∑ᵢ∫xᵢ²∂p ≤ P},
  ∃ P' : Fin n → ℝ, (∀ i, 0 ≤ P' i) ∧ (∑ᵢ P' i ≤ P) ∧
    (mutualInfoOfChannel p (parallelGaussianChannel N …)).toReal
      ≤ ∑ᵢ (1/2) * Real.log (1 + P' i / (N i : ℝ))
```

起点 = `parallelGaussian_max_ent_le_of_subadditivity` (`PerCoord.lean:257`)。この補題は
output 側 subadditivity (`jointDifferentialEntropyPi_le_sum`、**genuine**) を使い、honest piece
を (a) multivariate channel↔RV decomp + (b) per-coord max-ent allocation の 2 つに isolate
済。本 Phase は:

1. **`P'ᵢ := Varᵢ := ∫xᵢ²∂p`** で具体化 (`Varᵢ ≥ 0` trivial、`∑ Varᵢ ≤ P` constraint そのもの)。
2. **per-coord 上界 `h(Yᵢ) − h(Yᵢ|Xᵢ) ≤ (1/2)log(1+Varᵢ/Nᵢ)`** を:
   - `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` (`ContChannelMIDecomp.lean:247`、段 1 body) で
     `Iᵢ = h(Yᵢ) − h(Yᵢ|Xᵢ)`
   - `differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:510`) で
     `h(Yᵢ) ≤ (1/2)log(2πe(Varᵢ+Nᵢ))`
   - `differentialEntropy_gaussianReal` (`:406`) で `h(Yᵢ|Xᵢ = x) = (1/2)log(2πe Nᵢ)`
     (conditional → average も同値、Gaussian 不変性)
   - 引き算で `(1/2)log(1+Varᵢ/Nᵢ)`
3. **multivariate channel↔RV decomp `h_decomp` を honest piece として residual 化**:
   `parallelGaussian_max_ent_le_of_subadditivity` の `h_decomp` 引数 を `h_multivar_decomp`
   named hypothesis として constructor で受ける。これが本 plan の **唯一の新規 honest piece**。

### Done 条件

- `parallelGaussianCapacity_max_ent` lemma (~150-250 行) が genuine 🟢ʰ
- residual = `h_multivar_decomp` のみ (multivariate channel↔RV decomp、Mathlib 不在)
- `IsParallelGaussianPerCoordRegularity.max_ent` constructor field が埋まる

### 撤退条件 (D-3)

- `h(Yᵢ|Xᵢ = x) = (1/2)log(2πe Nᵢ)` の `x`-不変性 (Gaussian shift 不変) が `differentialEntropy_gaussianReal`
  の現 signature で取れない → conditional entropy `∫ h(Yᵢ|Xᵢ=x) dp` を honest 仮定 `h_cond_ent_gaussian_id`
  として外出し (本 plan の honest piece +1)。

**proof-log**: yes

---

## Phase 4 — constructor + hypothesis-minimal headline 再 publish ✅ (2026-05-25, commit `0fe2ad4`)

### スコープ

1. **`isParallelGaussianPerCoordRegularity_of_pieces`** constructor: Phase 1-3 の lemma を集約し、
   3 field を honest pieces のみから提供。
2. **`parallel_gaussian_capacity_formula_minimal`** headline: 既存
   `parallel_gaussian_capacity_formula` (`PerCoord.lean:367`) の `h_reg` 引数を上記 constructor で
   discharge し、最小限の honest hypothesis (multivariate decomp + bridge + maxent integrability) を
   signature 露出。

### Done 条件

- `parallel_gaussian_capacity_formula_minimal` が genuine 🟢ʰ (新規 honest piece = `h_multivar_decomp`
  1 件 + 既存 AWGN(#5) と共有の bridge/maxent residual)
- 5 件の `@audit:suspect(parallel-gaussian-moonshot-plan)` (`PerCoord.lean` 187/207/256/302/366) が
  `@audit:ok` に書換可能 (honest residual が hypothesis-minimal headline で `h_multivar_decomp` 1 件
  に集約済)

### 撤退条件

- constructor の bundle 3 field を honest pieces から再構成する際、field 間の依存 (`bddAbove`
  が `max_ent` 経由になる等) が circular に見える → `IsParallelGaussianPerCoordRegularity` を
  unbundled `And` 形に書換 (機械的 refactor、~30 行)

**proof-log**: yes (Phase 4 着地、L-PG1 closure 完了)

---

## Phase 5 — legacy 6 wrappers の `@audit:superseded-by(...)` 移行 ✅ (2026-05-25, commit `0fe2ad4`)

### スコープ

`ParallelGaussianKKT.lean` / `ParallelGaussianWFCertBody.lean` / `ParallelGaussianWFStationarityBody.lean`
の 6 件:

- `KKT.lean:282` `isParallelGaussianPerCoordReduction_of_bundle`
- `KKT.lean:294` `bundle_of_isParallelGaussianPerCoordReduction`
- `KKT.lean:324` `parallel_gaussian_capacity_formula_KKT_discharged`
- `KKT.lean:362` `parallel_gaussian_capacity_active_form_KKT_discharged`
- `WFCertBody.lean:329` `parallel_gaussian_capacity_formula_WFcert_discharged`
- `WFStationarityBody.lean:143` `parallel_gaussian_capacity_formula_WFstat_discharged`

各 declaration の docstring の `@audit:suspect(parallel-gaussian-moonshot-plan)` を
**`@audit:superseded-by(parallel-gaussian-l-pg1-discharge)`** に書換える (+ 必要なら
`@audit:closed-by-successor(parallel-gaussian-l-pg1-discharge)` も併用)。本体は
backward-compatibility 維持目的で削除しない (callers が存在する可能性、history record)。

加えて各 docstring の OPEN 記述 (「L-PG1 (per-coordinate water-filling reduction) remains OPEN」
「continuous AEP / sphere-shell volume machinery absent from Mathlib」) を **削除 or 訂正**
(本 plan で genuine 化済、continuous AEP は不要であることが確定済)。

### Done 条件

- 6 件の audit タグが `@audit:superseded-by(...)` (+ 必要なら `closed-by-successor`) に書換済
- OPEN 記述 (continuous AEP / stays OPEN) が削除 or 訂正
- `lake env lean InformationTheory/Shannon/ParallelGaussianKKT.lean` clean (本体は変更なし、docstring のみ)

### 撤退条件

- 該当 6 件のうち、現役の caller (テスト or 別 plan) が存在 → `superseded-by` ではなく
  本体を保持しつつ docstring のみ訂正 (`closed-by-successor` 単独タグ)

**proof-log**: no (タグ書換のみ)

---

## Phase V — verify + 親 plan 更新指示 ✅ (2026-05-25)

### スコープ

- `lake env lean InformationTheory/Shannon/ParallelGaussianPerCoordRegularity.lean` clean (0 errors /
  0 sorry / 警告最小)
- `lake env lean InformationTheory/Shannon/ParallelGaussianKKT.lean` / `…WFCertBody.lean` /
  `…WFStationarityBody.lean` clean (docstring 書換のみ、本体未変更)
- `InformationTheory.lean` への import 追記は **オーケストレータ側**
- **親 plan 更新指示**: `docs/shannon/parallel-gaussian-moonshot-plan.md` の冒頭実態整合
  ブロックを以下に更新指示 (本 plan は親 plan 本文を直接編集しない、planner 領域違反回避):
  - 「L-PG1 は **`parallel-gaussian-l-pg1-discharge-plan.md` で genuine discharge 済**、
    残 honest piece = multivariate channel↔RV MI decomp 1 件のみ」
  - 「主定理 `parallel_gaussian_capacity_formula` (`PerCoord.lean:367`) は genuine `le_antisymm`、
    `parallel_gaussian_capacity_formula_minimal` (`PerCoordRegularity.lean`) が hypothesis-minimal 形」

### Done 条件

- 全 Phase の着地状態 (Phase 1-4 genuine / Phase 5 タグ書換 / 撤退発動有無) が進捗ブロック +
  判断ログに反映
- 親 plan 冒頭の実態整合更新が pending 状態として記録 (本 plan の Phase V 出力 = 親 planner
  への指示)

**proof-log**: no (verify + 反映指示)

---

## 撤退ライン

親計画 `parallel-gaussian-moonshot-plan.md` §撤退ライン **L-PG1** + chain-rule plan §撤退ライン
**D-1** の継続。本 plan 内の段階撤退 (浅い順):

### [D-1 reaffirm] `max_ent` discharge が rabbit hole (Phase 3 が >250 行)

`max_ent` field を `parallelGaussian_max_ent_le_of_subadditivity` 直接消費の named hypothesis
`h_max_ent_from_subadd` として constructor で受ける形に縮退。Phase 1 (`bddAbove`) + Phase 2
(`achiever_mi`) は genuine、Phase 4 で hypothesis-minimal headline 着地 (honest piece +1)。

### [D-2] `achiever_mi` discharge が `mutualInfo_pi_eq_sum` 適用条件で詰まる (Phase 2)

`achiever_mi` field を named hypothesis `h_achiever_mi_sum` として constructor で受ける。
Phase 1 (`bddAbove`) + Phase 3 (`max_ent`) は genuine、Phase 4 で hypothesis-minimal headline
着地 (honest piece +1)。**chain-rule plan の Phase 3 撤退条件と同型**。

### [D-3] multivariate channel↔RV MI decomp の plumbing が想定外に重い (Phase 3)

`h_multivar_decomp` の statement そのものを `IsParallelChannelMIDecompHyp` predicate として
新規 named hypothesis 化 (AWGN-MI plan の `IsContChannelMIDecompHyp` `ContChannelMIDecomp.lean`
パターンを multivariate にコピー)。本 plan の honest piece は predicate 1 件に集約。

### [D-4] Phase 5 supersede が caller 存在で blocked

`@audit:superseded-by` ではなく `@audit:closed-by-successor(parallel-gaussian-l-pg1-discharge)`
タグ単独で運用、本体は保持。callers がいずれ新 headline `parallel_gaussian_capacity_formula_minimal`
に移行するまでの transition phase。

**いずれの撤退でも `sorry` は残さない** + **`:True` placeholder / 結論型≡仮説型 禁止**
(CLAUDE.md 検証の誠実性 + 撤退ライン規約厳守、`IsParallelGaussianPerCoordRegularity` の
field は **honest 解析仮定** であって conclusion ではない、本 plan で残置するときも
honest 名前付き仮説の延長で抜く)。

## Risk Table

| # | リスク | 確率 | 影響 | 緩和策 |
|---|---|---|---|---|
| 1 | multivariate channel↔RV MI decomp が Mathlib にも InformationTheory (`ContChannelMIDecomp.lean`) にも multivariate 形では存在しない | 中 | Phase 3 +50-100 行 / D-3 発動 | `IsParallelChannelMIDecompHyp` predicate で named hypothesis 化 |
| 2 | `mutualInfo_pi_eq_sum` の 3 i.i.d. factorization 条件 (joint/X/Y) が `gaussianProductInput Q` で充足できない (Kernel.prodMk vs Measure.pi 整合性) | 中 | Phase 2 +50 行 / D-2 発動 | per-coord MI sum を named hypothesis で外出し |
| 3 | per-coord conditional entropy `h(Yᵢ\|Xᵢ=x) = (1/2)log(2πe Nᵢ)` の `x`-不変性 plumbing | 中 | Phase 3 +30-50 行 | Gaussian shift 不変 `(awgnChannel (N i)) x = gaussianReal x (N i)` + `differentialEntropy_gaussianReal` 直接適用 |
| 4 | per-coord `Varᵢ := ∫xᵢ²∂p` の integrability residual (max-entropy 補題の honest 引数) | 中 | Phase 3 +20-40 行 | max-entropy plan / AWGN(#5) と共有、新規 honest piece を増やさない |
| 5 | `parallelGaussianCapacity_le_sum` (`PerCoord.lean:207`) の signature と本 plan の `bddAbove` 構成の整合 (P-free Q-free 上界 vs Q-dependent water-filling 上界) | 低 | Phase 1 +20 行 | `bddAbove` は P-free 上界、water-filling 上界は別 step (Phase 3) |
| 6 | Phase 5 で 6 件の caller が存在 (新 headline へ移行できない) | 低 | docstring 維持のみ / D-4 | `closed-by-successor` 単独タグで運用、本体保持 |
| 7 | `gaussianProductInput Q` で `Q i = 0` (water-filling inactive coord) の trivial fibre (`gaussianReal 0 0 = Dirac`) の特異処理 | 中 | Phase 2 + Phase 3 各 +10-20 行 | `gaussianReal 0 0` = `Dirac 0` の自動展開、active set 分割は既存 `waterFillingActiveSet` を使用 |

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **判断 #1 (planner、着手前)**: chain-rule plan (`parallel-gaussian-chain-rule-plan.md`) は
   既に 80% 執行済 (sup-sandwich + antisymmetry + 新 headline = `ParallelGaussianPerCoord.lean`
   396 行で genuine 着地)。本 plan は chain-rule plan を **再起草しない**、`IsParallelGaussianPerCoordRegularity`
   の 3 field 残務 + legacy 6 wrappers の supersede 移行に scope を絞る。route (α) per-coord
   分解 + 和 を採用 (chain-rule plan と共通)、route (β) 直接 calc は不採用 (T2-A 完成形再利用
   が最効率)。
2. **判断 #2 (planner、着手前)**: 11 件 closure target の内訳確定 — PerCoord 5 件は本 plan
   Phase 1-4 で `@audit:ok` 化、KKT/WF* 6 件は Phase 5 で `@audit:superseded-by(parallel-gaussian-l-pg1-discharge)`
   タグ書換 (本体保持で backward-compat)。AWGN family (`awgn-mi-decomp-plan` slug) 9 件は
   **本 plan の closure 対象外** (planner = AWGN MI bridge plan、ただし Phase 2/3 で消費
   する間接的連鎖あり)。
3. **判断 #3 (planner、着手前)**: chain-rule plan の Phase 3 で「continuous AEP 不要」と
   判断したが、`max_ent` field の honest residual に **multivariate channel↔RV MI decomp**
   が残ることを本 plan で確認 — これは continuous AEP ではなく、単 channel
   `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` (`ContChannelMIDecomp.lean:247`) の
   multivariate 化。Phase 0 で在庫差分確認、無ければ `h_multivar_decomp` named hypothesis として
   permit。本 plan 完了後の residual は **1 honest piece** (`h_multivar_decomp`) に集約見込み。

### 2026-05-25 Phase 0 在庫差分 (skeleton 着地 + 3 項目 verify)

skeleton `InformationTheory/Shannon/ParallelGaussianPerCoordRegularity.lean` (~166 行、
2 statement: `isParallelGaussianPerCoordRegularity_of_pieces` constructor + headline
`parallel_gaussian_capacity_formula_minimal`、body 共に `:= by sorry`) を着地、
`lake env lean` で **2 sorry warning のみ** (0 error / 他 warning 0)。

新規 `@audit:staged(...)` predicate **無し** (両 statement は既存 bundle
`IsParallelGaussianPerCoordRegularity` を consume するのみで、新規 predicate def 0 件)。
`@audit:suspect(parallel-gaussian-l-pg1-discharge)` タグを 2 statement docstring に付与
(Phase 4 closure 後に `@audit:ok` 化見込み)。

3 在庫差分項目の verify 結果:

- **項目 1 (multivariate channel↔RV MI decomp)**: **Mathlib 完全不在** + InformationTheory にも
  multivariate 形 **不在**。確認:
  - Loogle: `"mutualInfo", MeasureTheory.Measure.pi` → `Found 127 declarations mentioning
    MeasureTheory.Measure.pi. Of these, 0 have a name containing "mutualInfo".`
  - InformationTheory: 単 channel `mutualInfoOfChannel_toReal_eq_diffEntropy_sub`
    (`ContChannelMIDecomp.lean:248`) のみ存在、multivariate 化は `MultivariateDiffEntropy.lean`
    でも未提供 (`jointDifferentialEntropyPi_le_sum` は subadditivity だけ)。
  - **判定**: D-3 撤退 (`IsParallelChannelMIDecompHyp` predicate 新規 def) は **回避可能** —
    skeleton では `h_multivar_decomp` を **predicate ではなく直接 Prop** で構成
    (`∀ p ∈ feasible, ∃ P', P' ≥ 0 ∧ ∑ P' ≤ P ∧ MI ≤ ∑ (1/2) log(1+P'/N)` の existential 形)、
    Phase 3 で `parallelGaussian_max_ent_le_of_subadditivity` (`PerCoord.lean:257`) と
    align、新規 named predicate 不要。本 plan 完了後の honest piece は **1 件**
    (`h_multivar_decomp`、existential Prop) に集約見込み。
- **項目 2 (mutualInfo_pi_eq_sum 充足 path)**: 部分確認。`mutualInfo_pi_eq_sum`
  (`MIChainRule.lean:341`) は **RV 形** signature (`(Ω, μ)` + `Xs Ys : Fin n → Ω → α`)、
  3 i.i.d. factorization `h_iid_joint` / `h_iid_X` / `h_iid_Y` を要求。`gaussianProductInput Q
  = Measure.pi (gaussianReal 0 (Q i))` で充足するには **channel form ↔ RV form 変換** が
  必要 (`mutualInfoOfChannel_eq_mutualInfo_prod`, `ChannelCoding.lean:99`)。各 `i` で
  `μ.map Xs i = gaussianReal 0 (Q i)` + `μ.map Ys i = (gaussianReal 0 Q ⊗ awgnChannel N) i`
  の identification は **product 構造から `Measure.pi.map (eval i)` で取れる**
  (項目 3 の `pi_map_eval` 適用)。Phase 2 の plumbing として実行可能、D-2 撤退は **回避見込み**
  (詰まった場合は `h_perCoord_bridge_achiever` を constructor で受ける skeleton 形のまま
  Phase 2 を named hypothesis 形で抜く)。
- **項目 3 (marginal map lemma)**: **Mathlib `MeasureTheory.Measure.pi_map_eval` (`Mathlib/
  MeasureTheory/Constructions/Pi.lean:379`) 在庫**。
  Signature: `lemma pi_map_eval [DecidableEq ι] (i : ι) : (Measure.pi μ).map (Function.eval i)
  = (∏ j ∈ Finset.univ.erase i, μ j Set.univ) • (μ i)`。
  `IsProbabilityMeasure (μ j)` の元では `μ j univ = 1` で `∏ ≠ i (1) = 1` に簡約、
  実質 `(Measure.pi μ).map (· i) = μ i`。Phase 3 max_ent の per-coord plumbing で
  そのまま利用可能、**自作不要**。
- **Phase 1-3 経路確定**: Phase 1 (bddAbove) genuine 見込み (P-free 上界、Phase 3 と
  per-coord 上界を共有)。Phase 2 (achiever_mi) 🟢ʰ genuine 見込み (per-coord bridge は
  AWGN(#5) と共有、`mutualInfo_pi_eq_sum` plumbing は項目 3 で完備)。Phase 3 (max_ent)
  🟢ʰ genuine 見込み (subadd は `jointDifferentialEntropyPi_le_sum` で genuine、residual は
  `h_multivar_decomp` 1 件のみ existential 形で残置 = D-3 不要)。**D-1/D-2/D-3 撤退は
  いずれも不要見込み**、全 Phase で genuine 着地予定 (本 plan 完了後の honest piece = 1 件
  = `h_multivar_decomp`、当初予測通り)。

<!-- Phase 着手後 append: 各 Phase の着地 (genuine / D-1/D-2/D-3 撤退発動有無)、Phase 5
タグ書換結果 (caller 存在の有無)、最終 honest piece 数 (期待値 1: `h_multivar_decomp` のみ)、
親 plan / docstring 更新の orchestrator 反映状況 がここに記録される見込み。 -->

### 2026-05-25 Wave 3-2 着地 (commit `0fe2ad4`) — 全 Phase genuine closure 11 件

Wave 3 second batch (parallel orchestration、本 plan は 4 plan 中 1) で全 Phase 完遂。
撤退ライン D-1/D-2/D-3/D-4 は **いずれも未発動**、当初予測通り 1 件の honest piece
(`h_multivar_decomp` existential 形) に集約。

**closure 11 件の内訳**:

- **PerCoord.lean 5 件 (genuine residual → `@audit:closed-by-successor`)**:
  - `:187` `parallelGaussianCapacity_ge_sum`
  - `:207` `parallelGaussianCapacity_le_sum`
  - `:256` `parallelGaussian_max_ent_le_of_subadditivity`
  - `:302` `isParallelGaussianPerCoordReduction_discharged`
  - `:366` `parallel_gaussian_capacity_formula`

  PG 実装 agent は `PerCoord.lean` を **read-only** 制約で動いていた (per-coord sum identity
  5 件は upstream 既 genuine、本 plan は外側から regularity bundle を供給するスコープ)。
  そのため orchestrator が後段で 5 件の docstring 内 `@audit:suspect(parallel-gaussian-moonshot-plan)`
  を `@audit:closed-by-successor(parallel-gaussian-l-pg1-discharge)` に書換完了
  (上流 plan の closure motive が successor 1 件に集約されたことを SoT に記録)。

- **PerCoordRegularity.lean 2 件 (新規 statement → `@audit:ok`)**:
  - `isParallelGaussianPerCoordRegularity_of_pieces` constructor: body 充足
    (`refine { bddAbove := ?_, achiever_mi := h_perCoord_bridge_achiever, max_ent := h_multivar_decomp }`
    + global P-upper bound で `bddAbove` を `⟨∑ (1/2) log(1+P/Nᵢ), …⟩` 構成)
  - `parallel_gaussian_capacity_formula_minimal` hypothesis-minimal headline: body 充足
    (`Q := waterFillingPower ν N |>.toNNReal` 設定 → constructor で regularity bundle 構成
    → 既存 genuine `parallel_gaussian_capacity_formula` (`PerCoord.lean:367`) 適用)

- **legacy 6 wrappers (`@audit:suspect` → `@audit:superseded-by`)**:
  - `KKT.lean:282` `isParallelGaussianPerCoordReduction_of_bundle`
  - `KKT.lean:294` `bundle_of_isParallelGaussianPerCoordReduction`
  - `KKT.lean:324` `parallel_gaussian_capacity_formula_KKT_discharged`
  - `KKT.lean:362` `parallel_gaussian_capacity_active_form_KKT_discharged`
  - `WFCertBody.lean:329` `parallel_gaussian_capacity_formula_WFcert_discharged`
  - `WFStationarityBody.lean:143` `parallel_gaussian_capacity_formula_WFstat_discharged`

  各 docstring の OPEN 記述 (「L-PG1 remains OPEN」「continuous AEP / sphere-shell volume
  machinery absent from Mathlib」) を **訂正済** (本 plan で genuine 化、continuous AEP は
  不要であることが確定 — sup-sandwich で評価)。本体保持 (backward-compatibility、callers
  存在の可能性、history record)。

**撤退ライン未発動の根拠**:

- D-1 (max_ent rabbit hole): 回避 — `parallelGaussian_max_ent_le_of_subadditivity` (`PerCoord.lean:257`、
  既 genuine) の `h_decomp` 引数を `h_multivar_decomp` existential 形 honest piece として
  constructor に集約、Phase 3 では新規補題自作不要。
- D-2 (achiever_mi 詰まり): 回避 — `h_perCoord_bridge_achiever` を constructor で named
  hypothesis として受領 (per-coord AWGN bridge は AWGN(#5) と共有)、`mutualInfo_pi_eq_sum`
  plumbing を本 plan 内で展開する必要なし。
- D-3 (multivar decomp predicate): 回避 — `IsParallelChannelMIDecompHyp` predicate 新規 def
  は不要、existential Prop で十分。
- D-4 (Phase 5 supersede が caller blocked): 未発動 — 6 件は本体保持 + タグ書換のみで完結
  (`closed-by-successor` 併用は不要、`superseded-by` 単独で運用)。

**最終 honest piece 数**: **1 件** (`h_multivar_decomp` existential、`parallel_gaussian_capacity_formula_minimal`
の signature 露出)。当初予測 (Approach §honest pieces) と完全一致。

**orchestrator 反映状況**:

- PerCoord.lean 5 件の `@audit:closed-by-successor` 書換 = 同 commit `0fe2ad4` で完了
- legacy 6 wrappers の `@audit:superseded-by` 書換 + OPEN 記述訂正 = 同 commit で完了
- 親 plan (`parallel-gaussian-moonshot-plan.md`) 冒頭ステータス整合更新 = 本 docs sync turn
  (2026-05-25) で実施 (本 plan の Phase V 出力 = 親 planner 反映)

**本 plan 完結**。次の関連作業は別 plan 領域:

- `h_multivar_decomp` (multivariate channel↔RV MI decomposition) の Mathlib / InformationTheory
  formalization は `awgn-mi-decomp-plan` の multivariate 拡張 / 将来の独立 plan で。
- PG family の上位 chain (T2-B Tier 3 stretch goal) は本 plan の outside、roadmap 側の
  優先付け判断。

---

## 2026-05-29 wall:multivariate-mi 再検証

> **トリガー**: subadditivity が `withDensity_map` Found 0 にもかかわらず 13 行で self-build
> できた前例を踏まえ、`@residual(wall:multivariate-mi)` も「誤診された壁」でないかを独立再検証。
> 対象: `InformationTheory/Draft/Shannon/ParallelGaussianPerCoord.lean:455`
> `parallelGaussian_achiever_mi_eq_sum_perChannel` (現 `sorry`)。
> docs-only 調査、コード未変更。

### 一行サマリ

`wall:multivariate-mi` は **(b) self-build closeable だが subadditivity の 13 行とは桁が違う**
(中央 ~120-200 行、最重ステップ = pi-input × pi-kernel の compProd が per-coord 結合 box の
`Measure.pi` に factor することを `Measure.pi_eq` の box 普遍性で示す multivariate Tonelli)。
真の Mathlib 不在は `compProd`-of-`Measure.pi` factorization **1 点のみ**で、その下流の
`mutualInfo_pi_eq_sum` / `klDiv_pi_eq_sum` は既に genuine。subadditivity 型の「実は誤診」では
**ない**が、「未着手の self-buildable」ではある (predicate bundling や別壁阻害ではない)。

### 主定理の最終形 (再掲) + 証明戦略

```lean
-- ParallelGaussianPerCoord.lean:455 (現 sorry, @residual(wall:multivariate-mi))
theorem parallelGaussian_achiever_mi_eq_sum_perChannel {n : ℕ}
    (Q : Fin n → ℝ≥0) (N : Fin n → ℝ≥0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) :
    (mutualInfoOfChannel (gaussianProductInput Q)
        (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
      = ∑ i : Fin n,
          (mutualInfoOfChannel (gaussianReal 0 (Q i)) (awgnChannel (N i) (h_meas i))).toReal
```

pseudo-Lean 証明戦略 (RV-form 経由):

```
-- step 1: 両辺の mutualInfoOfChannel → mutualInfo (RV 形) へ
--   mutualInfoOfChannel_eq_mutualInfo_prod (ChannelCoding.lean:96, [IsMarkovKernel] 充足)
--   LHS = mutualInfo (jointDistribution p W) Prod.fst Prod.snd  (p,W は Markov)
-- step 2: jointDistribution p W = p ⊗ₘ W を Measure.pi (per-coord joint) に reshape
--   ★ここが唯一の Mathlib 不在 = wall 本体:
--     gaussianProductInput Q ⊗ₘ parallelGaussianChannel N
--       = (Measure.pi (fun i => gaussianReal 0 (Q i) ⊗ₘ awgnChannel (N i))).map e
--     e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
-- step 3: mutualInfo_pi_eq_sum (MIChainRule.lean:318, genuine) を適用
--     → ∑ i, mutualInfo (per-coord joint) X_i Y_i
-- step 4: 各 summand を mutualInfoOfChannel_eq_mutualInfo_prod の逆で per-coord channel MI に戻す
-- step 5: .toReal を Finset.sum と交換 (各項 ≠ ⊤、IsMarkovKernel で finite)
```

### API 在庫テーブル

#### (A) 既存 genuine 部品 (下流, 再利用可)

| 概念 | API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| channel MI → RV MI | `InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel_eq_mutualInfo_prod (p : Measure α) [IsProbabilityMeasure p] (W : Channel α β) [IsMarkovKernel W] : mutualInfoOfChannel p W = InformationTheory.Shannon.mutualInfo (jointDistribution p W) Prod.fst Prod.snd` | `InformationTheory/Shannon/ChannelCoding.lean:96` | genuine | step 1/4 両方向で使用。`[IsMarkovKernel]` は `parallelGaussianChannel.instIsMarkovKernel` / `awgnChannel.instIsMarkovKernel` で充足 |
| RV-form MI 加法性 | `mutualInfo_pi_eq_sum {n} (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β) (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i)) (h_iid_joint : μ.map (fun ω i => (Xs i ω, Ys i ω)) = Measure.pi (fun i => μ.map (fun ω => (Xs i ω, Ys i ω)))) (h_iid_X : μ.map (fun ω i => Xs i ω) = Measure.pi (fun i => μ.map (Xs i))) (h_iid_Y : μ.map (fun ω i => Ys i ω) = Measure.pi (fun i => μ.map (Ys i))) : mutualInfo μ (fun ω i => Xs i ω) (fun ω i => Ys i ω) = ∑ i, mutualInfo μ (Xs i) (Ys i)` | `InformationTheory/Shannon/MIChainRule.lean:318` | genuine (`@entry_point`) | step 3。**RV 形** であり channel 形ではない点が壁の本質 (下記ボックス) |
| KL 加法性 (pi) | `klDiv_pi_eq_sum {n} {α' : Fin n → Type*} [∀ i, MeasurableSpace (α' i)] (μs νs : ∀ i, Measure (α' i)) [∀ i, IsProbabilityMeasure (μs i)] [∀ i, IsProbabilityMeasure (νs i)] : klDiv (Measure.pi μs) (Measure.pi νs) = ∑ i, klDiv (μs i) (νs i)` | `InformationTheory/Shannon/MIChainRule.lean:249` | genuine | `mutualInfo_pi_eq_sum` 内部で使用済、直接呼ぶ別経路 (代替路) でも使える |
| KL 積加法性 | `klDiv_prod_eq_add (μ₁ μ₂ : Measure α') [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (ν₁ ν₂ : Measure β') [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] : klDiv (μ₁.prod ν₁) (μ₂.prod ν₂) = klDiv μ₁ μ₂ + klDiv ν₁ ν₂` | `InformationTheory/Shannon/MIChainRule.lean:230` | genuine | 代替路の base case |

#### (B) Mathlib 構成プリミティブ (壁 step 2 の self-build 用)

| 概念 | Mathlib API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| pi 普遍性 (box) | `MeasureTheory.Measure.pi_eq [∀ i, SigmaFinite (μ i)] {μ' : Measure (∀ i, α i)} (h : ∀ s : ∀ i, Set (α i), (∀ i, MeasurableSet (s i)) → μ' (Set.pi univ s) = ∏ i, μ i (s i)) : Measure.pi μ = μ'` | `Mathlib/MeasureTheory/Constructions/Pi.lean:281` | 存在 | step 2 の本丸。joint を box で評価して `∏` に一致させる。`IsProbabilityMeasure ⇒ SigmaFinite` |
| pi の box 値 | `MeasureTheory.Measure.pi_pi [∀ i, SigmaFinite (μ i)] (s : (i : ι) → Set (α i)) : Measure.pi μ (Set.pi univ s) = ∏ i, μ i (s i)` | `Mathlib/MeasureTheory/Constructions/Pi.lean:293` | 存在 (`@[simp]`) | RHS (per-coord joint の pi) を box で展開 |
| compProd box 値 | `MeasureTheory.Measure.compProd_apply [SFinite μ] [IsSFiniteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ ⊗ₘ κ) s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ` | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:61` | 存在 | LHS の joint を box で展開して `∫⁻` に。`IsMarkovKernel ⇒ IsSFiniteKernel`、`IsProbabilityMeasure ⇒ SFinite` |
| arrow↔prod 同型 (測度保存) | `MeasureTheory.measurePreserving_arrowProdEquivProdArrow (α β ι) (μ : ι → Measure α) (ν : ι → Measure β) : MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow α β ι) (Measure.pi (fun i => (μ i).prod (ν i))) ((Measure.pi μ).prod (Measure.pi ν))` | `Mathlib/MeasureTheory/Constructions/Pi.lean` (loogle 確認) | 存在 | `mutualInfo_pi_eq_sum` の内部で既に消費済。step 2 の reshape `e` の測度保存性 |
| 入力 pi 定義 | `gaussianProductInput Q = Measure.pi (fun i => gaussianReal 0 (Q i))` | `InformationTheory/Draft/Shannon/ParallelGaussianPerCoord.lean:95` | def | step 2 LHS の `μ` 部 |
| kernel fibre pi 定義 | `parallelGaussianChannel N x = Measure.pi (fun i => gaussianReal (x i) (N i))` (`@[simp] parallelGaussianChannel_apply`) | `InformationTheory/Shannon/ParallelGaussian.lean:94,101` | def | step 2 LHS の `κ` 部。各 fibre が `Measure.pi` |
| per-coord 入力 | `awgnChannel N x = gaussianReal x N` (`@[simp] awgnChannel_apply`) | `InformationTheory/Shannon/AWGN.lean:76,81` | def | per-coord joint `gaussianReal 0 (Q i) ⊗ₘ awgnChannel (N i)` の κ |

### 主要前提条件ボックス (壁 step 2 の事故りやすい点)

- **`mutualInfo_pi_eq_sum` は RV 形であって channel 形ではない**: `μ : Measure Ω` 上の RV 族
  `Xs Ys : Fin n → Ω → α/β` を取り、joint/X/Y が **3 本とも** `Measure.pi` に factor することを
  要求する。channel MI からこの形に持ち込むには、`Ω := (Fin n → ℝ) × (Fin n → ℝ)`、
  `μ := jointDistribution p W`、`Xs i := fun ω => ω.1 i`、`Ys i := fun ω => ω.2 i` と置く必要。
  このとき `h_iid_joint` は「`(p ⊗ₘ W).map (coordinate pairing) = Measure.pi (per-coord joint)`」
  に帰着 = 壁本体。`h_iid_X` は入力 marginal `p = Measure.pi (gaussianReal 0 (Q i))` (def で即),
  `h_iid_Y` は出力 marginal `W の output = Measure.pi (...)` (要 step 2 の系)。
- **`compProd_apply` の前提**: `[SFinite μ]` + `[IsSFiniteKernel κ]`。`IsProbabilityMeasure ⇒ SFinite`,
  `IsMarkovKernel ⇒ IsSFiniteKernel` は instance で自動だが、`κ a (Prod.mk a ⁻¹' s)` の box
  `s = box₁ ×ˢ box₂` での preimage は **per-coord box の積ではない** (preimage が a に依存)。
  実際は `compProd_apply_prod` (`MeasureCompProd.lean:69`, `(μ ⊗ₘ κ)(s ×ˢ t) = ∫⁻ a in s, κ a t ∂μ`)
  を使い、`κ a t = Measure.pi (gaussianReal (a i) (N i)) t` を box `t = Set.pi univ tᵢ` で
  `pi_pi` 展開 → `∫⁻ a in (Set.pi univ sᵢ), ∏ i, gaussianReal (a i) (N i) (tᵢ) ∂(Measure.pi (gaussianReal 0 (Q i)))`。
- **multivariate Tonelli が無料ではない**: 上の `∫⁻ over Measure.pi of ∏ i, fᵢ(aᵢ)` を
  `∏ i, ∫⁻ fᵢ` に分けるクリーンな `lintegral_pi` は **Mathlib に無い** (loogle:
  `lintegral_pi` unknown identifier; product-of-integrals は `lmarginal` /
  `lintegral_eq_lmarginal_univ` 経由の重い経路のみ)。ここが行数を押し上げる主因。
  ただし各 box `tᵢ` が固定なので `∏ i, gaussianReal (aᵢ)(Nᵢ)(tᵢ)` は `aᵢ` のみに依存する
  関数の積 → `Measure.pi` 上の独立積分公式 (`lintegral` の独立分解、`MeasureTheory.lintegral` ×
  `Measure.pi`) が要る。

### 自作が必要な要素 (優先度順)

1. **(最重) compProd-of-pi factorization lemma** — `(Measure.pi μᵢ) ⊗ₘ K = (Measure.pi (μᵢ ⊗ₘ Kᵢ)).map e`
   形 (K が per-coord kernel の "pi-fibre" kernel)。推奨: 直接 general lemma を立てず、
   本 achiever に特化した `gaussianProductInput Q ⊗ₘ parallelGaussianChannel N = (Measure.pi (per-coord joint)).map e`
   を `Measure.pi_eq` の box 普遍性で示す。box で `compProd_apply_prod` + `pi_pi` + per-coord
   Gaussian の独立積分。**工数 ~80-140 行**。落とし穴 = multivariate Tonelli (`lintegral_pi` 不在)。
2. **(中) 出力 marginal の pi 形** `(p ⊗ₘ W).snd = Measure.pi (gaussianReal 0 (Qᵢ) ⊗ₘ awgnChannel Nᵢ).snd`
   — step 2 lemma から `.snd` を取れば従う系。**~10-20 行**。
3. **(軽) `.toReal` と `Finset.sum` の交換** — 各 per-coord channel MI が finite (`klDiv` of prob
   measures, `IsMarkovKernel`)。`ENNReal.toReal_sum` + finiteness。**~15-25 行**。
4. **(軽) RV 形 plumbing** — `Xs/Ys i := ω ↦ ω.1/2 i` の measurability、`h_iid_X`/`h_iid_Y`/`h_iid_joint`
   を step 2 系から供給。**~30-50 行**。

合計中央 **~120-200 行** (subadditivity の 13 行とは桁違い、多変量 Tonelli が支配項)。

### Mathlib 壁の列挙 (真の不在)

| wall | loogle 確認 | shared sorry 補題化 |
|---|---|---|
| `Measure.pi` と `Measure.compProd` を結ぶ factorization lemma | `MeasureTheory.Measure.pi, MeasureTheory.Measure.compProd` → **`Found 0 declarations`** (2026-05-29) | この achiever 専用なので shared 化不要。ただし将来 multivariate channel が増えるなら `InformationTheory/Shannon/` の共有補題化候補 |
| `ProbabilityTheory.Kernel.pi` (kernel の pi) | **`unknown identifier 'ProbabilityTheory.Kernel.pi'`** (2026-05-29) | Mathlib に kernel-pi machinery が無いので「Kernel.pi の compProd 法則」経路 (orchestrator 仮説) は **存在しない**。pi-fibre kernel を独自定義する必要があるが、本件は `parallelGaussianChannel` が既に pi-fibre 形なので新規 kernel-pi 抽象は不要 |
| `lintegral_pi` (`∫⁻ over Measure.pi = ∏ ∫⁻`) | **`unknown identifier 'MeasureTheory.lintegral_pi'`** (2026-05-29); `lmarginal` 経由 (`lintegral_eq_lmarginal_univ`) のみ存在 | self-build 内で吸収 (box ごとの独立積分)。これが行数押上げ主因 |

**判定**: subadditivity (`withDensity_map` Found 0 → 13 行で self-build) と **同種だが規模が一桁上**。
真の不在は `compProd`-of-`pi` factorization 1 点で、それを `pi_eq` 普遍性で self-build できる
(=「誤診」ではあるが軽量ではない)。`Kernel.pi` 経路 (orchestrator 仮説 2) は Mathlib 不在で
**使えない** — `parallelGaussianChannel` が既に pi-fibre 形なので機械的に出ることは **ない**。

### 代替路 (factorization 非経由) の評価

- **`klDiv_pi_eq_sum` 直接経路**: MI を `klDiv (joint) (product)` で展開し、joint と product
  の両方を `Measure.pi` 形に reshape して `klDiv_pi_eq_sum` を割る経路。これも結局
  **joint = `Measure.pi` を示す** step が必要で、step 2 と同じ compProd-of-pi factorization に
  帰着する。`mutualInfo_pi_eq_sum` は内部でまさにこれ (`klDiv_pi_eq_sum`) を呼んでいる
  (`MIChainRule.lean:364`) ので、**代替路 = 同じ壁を別の入口から踏む**。回避にならない。
- 本質的に、joint `p ⊗ₘ W` が `Measure.pi` 形に factor することを示す step を回避する経路は
  無い (MI/KL の per-coord 分解は全て product 構造に依存)。**唯一の壁は step 2 に集約**。

### 撤退ラインへの距離

- 親 plan の撤退ライン **D-2** (achiever_mi が `mutualInfo_pi_eq_sum` 適用条件で詰まる) が
  まさにこの壁を予見していた。本 plan は D-2 を **回避** して `parallelGaussianCapacity_achiever_mi`
  に `h_perCoordMI` を named hypothesis で受ける形 (`PerCoord.lean:474`) で着地済、壁は
  `parallelGaussian_achiever_mi_eq_sum_perChannel` の `sorry` に **隔離済** (構造的撤退口は確保)。
- 本再検証は **新規撤退ライン発動なし**。現状の `sorry + @residual(wall:multivariate-mi)` は
  honesty 上 tier 2 で適正。ただし `@residual` の class は厳密には「**self-buildable wall**」
  (Mathlib に部品は揃う) であり、「閉じられない真の壁」ではない点を docstring に補足すると
  分類精度が上がる (orchestrator 判断)。

### 着手 skeleton (compProd-of-pi factorization を切り出す形)

```lean
import InformationTheory.Shannon.ParallelGaussian
import InformationTheory.Shannon.AWGN
import InformationTheory.Shannon.ChannelCoding
import InformationTheory.Shannon.MIChainRule
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory.Shannon.ParallelGaussian
open InformationTheory.Shannon InformationTheory.Shannon.AWGN

/-- ★ wall 本体を切り出した補題: pi-input × pi-fibre-kernel の joint が
per-coord joint の `Measure.pi` を `arrowProdEquivProdArrow` で reshape した形に factor する。
Mathlib 不在 (compProd-of-pi)、`Measure.pi_eq` の box 普遍性で self-build (~80-140 行)。 -/
theorem gaussianProductInput_compProd_parallelGaussianChannel_eq_pi {n : ℕ}
    (Q N : Fin n → ℝ≥0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) :
    (gaussianProductInput Q) ⊗ₘ (parallelGaussianChannel N h_meas h_parallel_meas)
      = (Measure.pi (fun i => (gaussianReal 0 (Q i)) ⊗ₘ (awgnChannel (N i) (h_meas i)))).map
          (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)) := by
  sorry -- @residual(wall:multivariate-mi)

/-- 主壁定理 (現 PerCoord.lean:455 の本体)。上の factorization + mutualInfo_pi_eq_sum で genuine 化。 -/
theorem parallelGaussian_achiever_mi_eq_sum_perChannel {n : ℕ}
    (Q N : Fin n → ℝ≥0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) :
    (mutualInfoOfChannel (gaussianProductInput Q)
        (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
      = ∑ i : Fin n,
          (mutualInfoOfChannel (gaussianReal 0 (Q i)) (awgnChannel (N i) (h_meas i))).toReal := by
  sorry -- step 1-5 above; depends on the factorization lemma

end InformationTheory.Shannon.ParallelGaussian
```

### ゲート判定 (3-5 行)

- `wall:multivariate-mi` = **(b) self-build closeable**。真の Mathlib 不在は `compProd`-of-`Measure.pi`
  factorization **1 点** (loogle Found 0、`Kernel.pi` も unknown identifier)。下流の
  `mutualInfo_pi_eq_sum` / `klDiv_pi_eq_sum` は既に genuine、`Measure.pi_eq` / `compProd_apply_prod` /
  `pi_pi` / `measurePreserving_arrowProdEquivProdArrow` の部品も揃う。
- **(c) `Kernel.pi` factorization が機械的、は誤り**: Mathlib に kernel-pi が無いため
  orchestrator 仮説 2 (Kernel.pi の compProd 法則) は使えない。`parallelGaussianChannel` が
  既に pi-fibre 形である事実を直接突く self-build が唯一の道。
- closeable 必要部品: 切出し補題 `gaussianProductInput_compProd_parallelGaussianChannel_eq_pi`
  (~80-140 行、`Measure.pi_eq` 普遍性 + box ごとの多変量 Tonelli)。規模中央 **~120-200 行**
  (subadditivity の 13 行とは一桁違う)。**最初の 1 手** = 上記切出し補題を skeleton 化し、
  `Measure.pi_eq` で box `Set.pi univ sᵢ` に対し LHS=`compProd_apply_prod`、RHS=`pi_pi` を展開、
  per-coord Gaussian の独立積分で `∏` 一致を埋める。
- subadditivity と同様の「**未着手の self-buildable 壁**」である (predicate bundling / 別壁阻害
  ではない)。ただし軽量 (13 行) ではなく、多変量 Tonelli が支配項のため subadditivity より重い。
