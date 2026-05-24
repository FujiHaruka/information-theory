# Parallel Gaussian L-PG1 closure: regularity-bundle discharge + legacy retraction

> **Parent**: [`parallel-gaussian-moonshot-plan.md`](parallel-gaussian-moonshot-plan.md) §「撤退ライン discharge 子 plan へのポインタ」L-PG1。
>
> **Predecessor (already executed)**: [`parallel-gaussian-chain-rule-plan.md`](parallel-gaussian-chain-rule-plan.md)。
> ステップ1〜5 の sup-sandwich scaffolding は `Common2026/Shannon/ParallelGaussianPerCoord.lean`
> (396 行) で着地済。`isParallelGaussianPerCoordReduction_discharged` (`:303`) + 新 headline
> `parallel_gaussian_capacity_formula` (`:367`) は **genuine `le_antisymm`** に到達済 (旧 `:= h_per_coord`
> pass-through は retracted、`ParallelGaussian.lean:245-256` の retracted comment 参照)。
>
> **本 plan のスコープ**: `IsParallelGaussianPerCoordRegularity` (`PerCoord.lean:156`) の **3 つ
> の honest field 残務**を closure する + 親 plan の **6 件の legacy passthrough wrapper を
> `@audit:superseded-by` で正式 retract** する。chain-rule plan の Phase 4 撤退ライン D-1 を
> 確定的に通り抜ける段階。
>
> **Status (2026-05-24)**: 着手前。route (α) per-coord 分解 + 和 を採用 (chain-rule plan と
> 共通)。AWGN family (T2-A) 完成形 + `AWGNMIBridge.lean` + `MIChainRule.mutualInfo_pi_eq_sum`
> を最大限再利用、新規解析の量を最小化。

## 進捗

- [ ] Phase 0 — 在庫差分: `IsParallelGaussianPerCoordRegularity` 3 field の Mathlib + Common2026 在庫確認 📋
- [ ] Phase 1 — `bddAbove` discharge (analytic bound, 最軽量) 📋
- [ ] Phase 2 — `achiever_mi` discharge (product input MI = sum、`mutualInfo_pi_eq_sum` 適用) 📋
- [ ] Phase 3 — `max_ent` discharge (correlated-input upper bound、subadditivity 基盤利用、最重) 📋
- [ ] Phase 4 — `IsParallelGaussianPerCoordRegularity` constructor + headline 再 publish 📋
- [ ] Phase 5 — legacy 6 wrappers の `@audit:superseded-by(...)` 移行 📋
- [ ] Phase V — verify + 親 plan progress 更新指示 📋

## ゴール / Approach

### Goal (最終 signature)

新規ファイル `Common2026/Shannon/ParallelGaussianPerCoordRegularity.lean` で
`IsParallelGaussianPerCoordRegularity` の **constructor を honest pieces のみから** 提供し、
それを介して headline `parallel_gaussian_capacity_formula` の `h_reg` 引数を消去した
**hypothesis-minimal** 再 publish を出す:

```lean
namespace InformationTheory.Shannon.ParallelGaussian

open Common2026.Shannon ChannelCoding

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

新規 `Common2026/Shannon/ParallelGaussianPerCoordRegularity.lean`:

```
Common2026/Shannon/
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
Common2026.lean                      ← `import Common2026.Shannon.ParallelGaussianPerCoordRegularity`
                                         追記 (Phase V、オーケストレータ)
```

**新規 import (`ParallelGaussianPerCoordRegularity.lean`、CLAUDE.md `Import Policy` 厳守、pinpoint)**:

```lean
import Common2026.Shannon.ParallelGaussian
import Common2026.Shannon.ParallelGaussianPerCoord
import Common2026.Shannon.AWGN
import Common2026.Shannon.AWGNMIBridge
import Common2026.Shannon.ContChannelMIDecomp
import Common2026.Shannon.DifferentialEntropy
import Common2026.Shannon.MIChainRule
import Common2026.Shannon.MultivariateDiffEntropy
import Common2026.Shannon.ChannelCoding
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

- **multivariate channel↔RV MI decomposition** (`h_multivar_decomp` の Mathlib / Common2026 有無):
  単 channel `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` (`ContChannelMIDecomp.lean:247`) の
  **multivariate 化** が存在するか。無ければ honest 仮定として残す (新規 1 件)。
- **`Measure.pi` 上 `(· i)` marginal の `gaussianReal` への identification**: parallel input
  `p` の i-th marginal が `awgnChannel (N i)` output の law と整合する射影 (Phase 3 の per-coord
  上界 plumbing)。
- **`gaussianProductInput` の `Measure.pi` instance**: Phase 2 の `mutualInfo_pi_eq_sum`
  適用条件 (joint/X/Y i.i.d. factorization 3 本) を product Gaussian で充足することの確認。

---

## Phase 0 — 在庫差分 + skeleton 📋

### スコープ

着手前に 3 点を loogle + Read で verify:

1. **multivariate channel↔RV MI decomposition** の Mathlib / Common2026 在庫
   (`h_multivar_decomp` の名前付き仮説化 / genuine 化の判断材料)。
2. **`mutualInfo_pi_eq_sum` の 3 i.i.d. factorization 条件** を `gaussianProductInput Q` で
   充足する path (Phase 2 achiever_mi)。
3. **`(p : Measure (Fin n → ℝ)).map (· i)` の marginal lemma** (Phase 3 max_ent で
   per-coord 上界に落とす plumbing)。

### 成果物

- skeleton `Common2026/Shannon/ParallelGaussianPerCoordRegularity.lean` (constructor + headline +
  補助補題を `:= by sorry`、`isParallelGaussianPerCoordRegularity_of_pieces` /
  `parallel_gaussian_capacity_formula_minimal` を statement 完成)
- 本計画書への反映 (multivariate decomp の在庫有無 → Phase 3 の Approach / 撤退ライン D-3 の更新)

### Done 条件

- skeleton が `lake env lean` で sorry warning のみ
- 3 在庫差分項目が判断ログに記録 (Phase 1-3 の経路が確定)

**proof-log**: no (調査 + skeleton)

---

## Phase 1 — `bddAbove` discharge 📋

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

## Phase 2 — `achiever_mi` discharge 📋

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

## Phase 3 — `max_ent` discharge ★最重 📋

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

## Phase 4 — constructor + hypothesis-minimal headline 再 publish 📋

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

## Phase 5 — legacy 6 wrappers の `@audit:superseded-by(...)` 移行 📋

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
- `lake env lean Common2026/Shannon/ParallelGaussianKKT.lean` clean (本体は変更なし、docstring のみ)

### 撤退条件

- 該当 6 件のうち、現役の caller (テスト or 別 plan) が存在 → `superseded-by` ではなく
  本体を保持しつつ docstring のみ訂正 (`closed-by-successor` 単独タグ)

**proof-log**: no (タグ書換のみ)

---

## Phase V — verify + 親 plan 更新指示 📋

### スコープ

- `lake env lean Common2026/Shannon/ParallelGaussianPerCoordRegularity.lean` clean (0 errors /
  0 sorry / 警告最小)
- `lake env lean Common2026/Shannon/ParallelGaussianKKT.lean` / `…WFCertBody.lean` /
  `…WFStationarityBody.lean` clean (docstring 書換のみ、本体未変更)
- `Common2026.lean` への import 追記は **オーケストレータ側**
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
| 1 | multivariate channel↔RV MI decomp が Mathlib にも Common2026 (`ContChannelMIDecomp.lean`) にも multivariate 形では存在しない | 中 | Phase 3 +50-100 行 / D-3 発動 | `IsParallelChannelMIDecompHyp` predicate で named hypothesis 化 |
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

<!-- Phase 着手後 append: 各 Phase の着地 (genuine / D-1/D-2/D-3 撤退発動有無)、Phase 5
タグ書換結果 (caller 存在の有無)、最終 honest piece 数 (期待値 1: `h_multivar_decomp` のみ)、
親 plan / docstring 更新の orchestrator 反映状況 がここに記録される見込み。 -->
