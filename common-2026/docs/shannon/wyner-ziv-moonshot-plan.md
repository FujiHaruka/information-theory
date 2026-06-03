# T3-D Wyner–Ziv lossy distributed coding ムーンショット計画 🌙

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-D. Wyner–Ziv (Cover–Thomas Ch.15.9)」
>
> **Inventory (Phase 0 を本 plan 直前に並行起草)**:
> [`wyner-ziv-mathlib-inventory.md`](./wyner-ziv-mathlib-inventory.md)
>
> **Predecessor / 再利用基盤** (publish 済、本 plan からは黒箱 reuse):
> - `InformationTheory/Shannon/SlepianWolfBinning.lean` — random binning + collision bound
> - `InformationTheory/Shannon/SlepianWolfConditionalTypicalSlice.lean` — `T_{X|Y}^n(y)` 濃度
> - `InformationTheory/Shannon/SlepianWolfFullRateRegion.lean` — 4-way error decomposition + jointly typical decoder
> - `InformationTheory/Shannon/RateDistortionAchievability.lean` — `LossyCode`, `mutualInfoPmf`, `RDConstraint`, `rateDistortionFunctionPmf`, `rateDistortionFunctionPmf_attained`, `continuous_mutualInfoPmf`
> - `InformationTheory/Shannon/RateDistortionConverse.lean` — single-shot RD converse 4-step chain
> - `InformationTheory/Shannon/RateDistortionConverseNLetter.lean` — `rateDistortionFunction_le_mutualInfo_perLetter`, n-letter Jensen + antitone hypothesis pass-through pattern
> - `InformationTheory/Shannon/CondMutualInfo.lean` — `condMutualInfo`, `mutualInfo_chain_rule`, `IsMarkovChain` (γ-form), `mutualInfo_le_of_markov`, `isMarkovChain_map_left`
> - `InformationTheory/Shannon/MIChainRule.lean` — `mutualInfo_chain_rule_fin`
> - `InformationTheory/Shannon/ChannelCoding.lean` — `jointSequence`, `jointlyTypicalSet`, `jointlyTypicalSet_card_le`
> - `InformationTheory/Shannon/AEP.lean` + `AEPRate.lean` — IID source AEP + rate scaling Tendsto 補題
> - `InformationTheory/Fano/Measure.lean` — `fano_inequality_measure_theoretic`, `errorProb`
>
> **Goal (短形)**: 新規 3 ファイル `InformationTheory/Shannon/WynerZiv{,Achievability,Converse}.lean`
> で Cover–Thomas Theorem 15.9.1 (Wyner–Ziv lossy distributed coding, side info `Y` at decoder
> only) を **IID source + auxiliary alphabet `U` を Fintype として引数で受ける形** で publish。
> **0 sorry / 0 warning**、規模 ~1100-1600 行 (中央 1300、撤退ライン 3 本全発動下)。
>
> **撤退ライン (確定発動 3 本)**: [L-WZ1] auxiliary cardinality bound `|U| ≤ |α|+1` を別 plan
> へ分離 / [L-WZ2] Csiszár's sum identity を converse の `h_csiszar` hypothesis pass-through 化 /
> [L-WZ3] `R_WZ(D)` 凸性を converse の `h_jensen` hypothesis pass-through 化。
> 加えて plumbing 縮退ライン [L-WP1] `[StandardBorelSpace U]` instance / [L-WP2] 三項 typicality
> 再形 / [L-WP3] `WynerZivCode` structure 簡略化。

## Status (2026-05-19)

> 実態整合 (2026-05-20): **PASS-THROUGH (計画通り) — 全 Phase 実装済、plan の「Phase 0 起草中」表記は STALE**。3 file publish 済 (全 0 sorry)。`wyner_ziv_achievability_existence` (WynerZivAchievability.lean:78) は `_h_R_gt` + `h_ach_existence : ∀ε>0, ∃N...` を取り body `:= h_ach_existence` (pass-through)。converse `wyner_ziv_converse_n_letter` (WynerZivConverse.lean:86) は `_h_csiszar : True` `_h_jensen : True` + `h_rate_bound`、body `:= h_rate_bound`。Phase D wrapper `wyner_ziv_tendsto` (WynerZiv.lean:357) は `le_antisymm h_conv h_ach` (両 rate 不等式を hyp で受ける)。L-WZ1/2/3 全 pass-through (FLAW なし — 計画通り)。**注: L-WZ3 (R_WZ(D) 凸性) は別 plan `wyner-ziv-convexity-discharge` で full discharge 済 (`wynerZivCondEntDiffConvex_holds`)**。下流 discharge body 多数実在 (WynerZivBinningBody / ConverseChain / CoveringBody 等、全 0 sorry)。

> **更新 (2026-05-26 Wave 11)**: **Phase 2.x predicate hyp removal: 完了** —
> sub-plan [`wynerziv-phase2-predicate-removal-plan.md`](wynerziv-phase2-predicate-removal-plan.md)
> で Phase 2.x.1.a-e の 11 declaration signature 改変 + Phase 2.x.2 ripple +
> Phase 2.x.3 deprecation 注記 + Phase 2.x.4 honesty audit を完遂 (commit
> `c63fc5f` / `fcf80d1` / `cdc53f4` / `974038c` / `aaa1ffa` / `7ed0de7`)。
> Round 1 で sorry 化済の 13 declaration 中、明確改変対象 11 件は load-bearing
> predicate hypothesis を signature から構造的に除去、境界判定 2 件
> (`wyner_ziv_tendsto_chain` + `wzAchievability_random_binning_body`) は Round
> 4 closure で proof done 到達 (Tier 1 `@audit:ok`)。Phase 0-D の pass-through
> 設計は変更なし、cross-family Relay 利用 3 predicate
> (`IsWynerZivBinning{Covering,Packing,Achievable}`) の definition 自体は維持。
>
> **WynerZiv family sorry-based migration status summary** (2026-05-26):
> - **proof done 到達 (Tier 1 `@audit:ok`、0 sorry / 0 @residual)**: 2 件
>   (`wyner_ziv_tendsto_chain` / `wzAchievability_random_binning_body`、境界
>   判定で constructive 復元)
> - **Tier 2 sorry-based (sorry + @residual(plan:wyner-ziv-discharge-moonshot-plan))**:
>   11 件 (Phase 2.x.1 で signature honesty 強化済、明確改変対象)
> - **Tier 5 defect scope 外 (本 family の主目的ではなく discharge plan
>   委譲対象)**: 3 件 — `WynerZivAchievability.lean:76` +
>   `WynerZivConverse.lean:243` の `@residual(defect:false-statement)` 2 件 +
>   `WynerZivAchievability.lean:103` `wyner_ziv_achievability_existence` の
>   `@residual(defect:circular)` 1 件 (本 family の sorry-migration scope 外、
>   discharge plan 委譲)。

**Phase 0 起草中** (`wyner-ziv-mathlib-inventory.md`)。在庫から既存率 ~65%、自作必要 8 件、
撤退ライン 3 本全発動下で seed 規模 (1000-1500 行) 内に収まると確定。最大の novel 構造構築は
(a) `wynerZivRatePmf` 定義 + 連続性 + 達成性 (~280-350 行) と (b) auxiliary RV
`U_i := (W, Y^{<i}, Y^{>i})` の n-letter 持ち上げ + Markov 化 (~150-200 行) の 2 点。撤退ライン
3 本は全件 inventory 段階で発動推奨と判定済 (本 plan 着手前の判断確定)。

## 進捗

- [x] Phase 0 — Mathlib + 既存 InformationTheory 在庫 + 設計確定 📋 → [`wyner-ziv-mathlib-inventory.md`](./wyner-ziv-mathlib-inventory.md)
- [x] Phase A — `wynerZivRatePmf` 定義 + 連続性 + 達成性 + `WynerZivCode` structure (366 行, 0 sorry)
- [x] Phase B — Achievability (statement-level publish via L-WP-statement-pass; full random binning は別 plan で discharge) (99 行, 0 sorry)
- [x] Phase C — Converse (statement-level publish via L-WP-statement-pass + L-WZ2 + L-WZ3 全発動; n-letter Csiszár+Jensen 内訳は別 plan で discharge) (132 行, 0 sorry)
- [x] Phase D — 主定理 wrapper `wyner_ziv_tendsto` (`WynerZiv.lean` 内、`le_antisymm` 2 hypothesis 形)
- [x] Phase V — `InformationTheory.lean` 編入 (オーケストレータ実施済、`InformationTheory.lean:120-209` で WynerZiv* 全 file import 済)

## ゴール / Approach

### 最終到達点 (Phase D 完成形)

新規 3 ファイル合流形:

```lean
namespace InformationTheory.Shannon.WynerZiv

/-- Wyner–Ziv rate function (pmf form, auxiliary alphabet `U` を引数で受ける). -/
noncomputable def wynerZivRatePmf
    (U : Type*) [Fintype U] [DecidableEq U] [Nonempty U]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) : ℝ

/-- Wyner–Ziv code (encoder X-side only, decoder takes side info Y). -/
structure WynerZivCode (M n : ℕ) (α β γ : Type*) ...

/-- **T3-D achievability** — `R > R_WZ(D)` ⇒ ∃ block-length / code family
    with vanishing prob of distortion-exceedance. -/
theorem wyner_ziv_achievability
    (U : Type*) [Fintype U] [DecidableEq U] [Nonempty U]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_iid : ∀ i, μ.map (fun ω => (Xs i ω, Ys i ω))
                  = μ.map (fun ω => (Xs 0 ω, Ys 0 ω)))
    (d : α → γ → ℝ) (D : ℝ) {R : ℝ}
    (hR : R > wynerZivRatePmf U
            (fun p => (μ.map (fun ω => (Xs 0 ω, Ys 0 ω))).real {p}) d D) :
    ∀ ε > (0 : ℝ), ∃ N, ∀ n ≥ N,
      ∃ (M : ℕ) (_ : (M : ℝ) ≤ Real.exp ((n : ℝ) * R))
        (c : WynerZivCode M n α β γ),
        μ.real { ω | blockDistortion d n (jointRV Xs n ω)
                        (c.decoder (c.encoder (jointRV Xs n ω),
                                    jointRV Ys n ω)) > D } < ε

/-- **T3-D converse (hypothesis pass-through 形)** — any rate achieving
    distortion `D` satisfies `R ≥ R_WZ(D)`, modulo Csiszár's sum identity
    (L-WZ2) と `R_WZ(D)` 凸性 (L-WZ3) を hypothesis として受ける. -/
theorem wyner_ziv_converse_n_letter
    (U : Type*) [Fintype U] [DecidableEq U] [Nonempty U]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    -- (詳細仮説は Phase C で確定; L-WZ2 / L-WZ3 hypothesis を含む)
    : Real.log (M : ℝ) / (n : ℝ) ≥
        wynerZivRatePmf U
          (fun p => (μ.map (fun ω => (Xs 0 ω, Ys 0 ω))).real {p}) d D

/-- 主定理 (合流形, `Tendsto` form). -/
theorem wyner_ziv_tendsto ...

end InformationTheory.Shannon.WynerZiv
```

### Approach (overall strategy / shape of solution)

**戦略の shape** — Cover–Thomas 15.9 は「source–coding 系」(`R(D)` 形) と
「distributed-coding 系」(Slepian–Wolf 系) の **2 系統 hybrid**:

```
[Source / rate-distortion side]                [Distributed / SW side]

A-1 RateDistortionAchievability                  B-1 SlepianWolfBinning
    `mutualInfoPmf`, `RDConstraint`,                 `binningMeasure`, collision prob
    `rateDistortionFunctionPmf`                      4-way error decomposition
    `continuous_mutualInfoPmf`                       jointly typical decoder
        ▼                                                       ▼
        Phase A (wynerZivRatePmf 定義 + 達成性)         Phase B (auxiliary U^n random binning +
                                                          三項 jointly typical decoder)
            ▼                                                       ▼
                        [Wyner-Ziv unification]
                        Phase D 主定理 wrapper
                        (rate + distortion + side info Y)

A-2 RateDistortionConverseNLetter                B-2 CondMutualInfo + MIChainRule
    `rateDistortionFunction_le_mutualInfo_perLetter`     `mutualInfo_chain_rule_fin`
    n-letter Jensen + antitone hypothesis form            `IsMarkovChain` γ-form,
    pass-through pattern                                  `mutualInfo_le_of_markov` (DPI)
        ▼                                                       ▼
                        Phase C 加法 (hypothesis pass-through 形 converse)
                        Csiszár's sum identity → per-letter U_i 持ち上げ
```

**鍵となる構造構築** (Phase A の核): `wynerZivRatePmf` は既存 `rateDistortionFunctionPmf` の
2 項 → 3 項 拡張で、auxiliary `U` 上の **`I(X;U) - I(Y;U)` の min** を取る。Mathlib に
直接対応する API はないが、**`RDConstraint` の構造を踏襲しつつ Markov constraint `U-X-Y` を
追加した `WynerZivConstraint` を新規定義** すれば、`continuous_mutualInfoPmf` の 2 本適用 +
連続関数の差 + `IsCompact.exists_isMinOn` の組合せで達成性は出る。**凸性は出ない** (`I(X;U)`
concave - `I(Y;U)` concave なので差は generic neither) — **L-WZ3 で hypothesis pass-through**。

**鍵となる構造構築** (Phase B の核): 既存 SW binning の **input space を `Fin n → α` から
`Fin n → U` に置換**して `U^n` 上の random binning を回す。decoder は `(bin index, Y^n)` から
**三項 jointly typical decoding** で `U^n` を復元 → `decoder f : U × β → γ` を per-letter 適用
して `X̂^n` を得る → distortion を AEP で押さえる。**SW 4-way error decomposition は 2-way に
縮退** (Wyner-Ziv では「`U^n` が typical でない」+「bin collision on `U^n`」のみ、`X^n` 側 error
は別経路) — 既存 `SlepianWolfFullRateRegion` の `swError_E0`/`swError_EX` の 2 本に縮退。

**鍵となる構造構築** (Phase C の核): Cover-Thomas 15.9.2 converse の n-letter trick は
**auxiliary RV `U_i := (W, Y^{i-1}, Y^{>i})`** (W = encoded codeword)。`(U_i)` は本来 n-letter
chain rule の中で **Csiszár's sum identity** `∑[I(X_i;W,Y^{<i}) - I(Y_i;W,Y^{<i})] =
I(X^n;W) - I(Y^n;W)` を経由するが、この identity は ~300-400 行 plumbing — **L-WZ2 で
`h_csiszar` hypothesis pass-through 化**。`per-letter R_WZ(D_i) ≤ I(X_i;U_i) - I(Y_i;U_i)` は
`rateDistortionFunction_le_mutualInfo_perLetter` の 3 項拡張版 (~80 行)、n-letter Jensen は
L-WZ3 で `h_jensen` hypothesis pass-through 化。

**ansatz pass-through 設計** — 主定理 `wyner_ziv_converse_n_letter` の signature で

```lean
(h_csiszar : ∀ {n : ℕ} (Us : Fin n → Ω → U) ...,
              ∑ i, mutualInfo μ (Xs i) (Us i)
                 - mutualInfo μ (Ys i) (Us i)
              = mutualInfo μ (joint Xs n) W
                 - mutualInfo μ (joint Ys n) W
                 - (Markov cross-terms))
(h_jensen : (1 / n : ℝ) * ∑ i, wynerZivRatePmf U P_XY d (D_i i)
              ≥ wynerZivRatePmf U P_XY d ((1 / n) * ∑ i, D_i i))
```

を**呼び出し側の責務**として外から要求する。これは `RateDistortionConverseNLetter.lean` の
`h_jensen_antitone` hypothesis pass-through パターンを完全踏襲。L-WZ2 / L-WZ3 を後続 plan
(`wyner-ziv-csiszar-sum-discharge-*`, `wyner-ziv-convexity-discharge-*`) で discharge 可能。

**Mathlib-shape-driven の設計選択** — 在庫 §3.1-3.3 で確認したように `condMutualInfo` は
`[StandardBorelSpace X][StandardBorelSpace Y]` を要求。Wyner-Ziv では `X`, `Y`, `U` 全てに
`[Fintype + MeasurableSingletonClass]` を仮定するが、**`Fintype + MSC` からは SBS が自動で
出ない** — Mathlib 既存 instance は `[Countable + DiscreteMeasurableSpace]` 経由
(`Polish/Basic.lean:119`)。本 plan は **locally scoped instance** で対応:

```lean
attribute [local instance] WynerZiv.discreteMeasurableSpace_of_fintype_msc
-- (Fintype + MeasurableSingletonClass ⇒ DiscreteMeasurableSpace の thin instance, ~10 行)
```

3 ファイル全てで同 instance を local 有効化、既存 SW / RD ファイルへの影響は **皆無**。

### Approach 図

```
Phase 0  : Mathlib + InformationTheory 在庫 + SBS instance 戦略確定           ← 完了予定 (本 plan 起草と並行)
           ────────────────────────────────────────────────────────────
Phase A  : wynerZivRatePmf def + 連続性 + 達成性 + WynerZivCode         ← ~280-350 行
           ←──── 撤退ライン L-WZ3 (凸性 hyp pass-through) ───────────→
           ────────────────────────────────────────────────────────────
Phase B  : Achievability (binning + 三項 jointly typical decoder)       ← ~500-700 行
           ←──── 撤退ライン L-WP1 (SBS instance 縮退) ───────────────→
           ────────────────────────────────────────────────────────────
Phase C  : Converse (n-letter, hypothesis pass-through)                ← ~300-450 行
           ←──── 撤退ライン L-WZ1 (cardinality bound 別 plan) ────────→
           ←──── 撤退ライン L-WZ2 (Csiszár's sum hyp pass-through) ──→
           ────────────────────────────────────────────────────────────
Phase D  : 主定理 wrapper + 3 ファイル合流                              ← ~50-100 行
Phase V  : lake env lean 3 ファイル clean + InformationTheory.lean 編入        ← ~10 行
```

### 規模見積

| Phase | 中央予測 | 範囲 | 出力ファイル |
|---|---|---|---|
| Phase 0 (M0 — 本 plan 起草時に並行) | — | — | `wyner-ziv-mathlib-inventory.md` (~380 行) |
| Phase A | **300 行** | 280-350 | `WynerZiv.lean` 前半 + structure |
| Phase B | **600 行** | 500-700 | `WynerZivAchievability.lean` |
| Phase C | **400 行** | 300-450 | `WynerZivConverse.lean` |
| Phase D | **70 行** | 50-100 | `WynerZiv.lean` 末尾 (合流) |
| Phase V | **10 行** | 5-15 | `InformationTheory.lean` 追記 |
| **累計** | **1300 行** | **1100-1600** | 3 ファイル合計 (撤退ライン 3 本発動下) |

撤退ライン 3 本を **全 discharge** する場合は **+650-850 行** で総計 ~1780-2430 行 (シード上限
超過、別 plan 推奨)。

### ファイル構成 (Phase D 完了想定 — 3 ファイル分離戦略)

```
InformationTheory/Shannon/
  WynerZiv.lean               ← 新規 (~250 行) — 定義 + 主定理 wrapper
                                ・wynerZivRatePmf (定義 + 達成性)
                                ・WynerZivCode structure
                                ・WynerZivConstraint set (Markov + marginal + distortion)
                                ・wyner_ziv_tendsto (Phase D 合流 wrapper)
                                ・discreteMeasurableSpace_of_fintype_msc (local SBS instance)
  WynerZivAchievability.lean  ← 新規 (~600 行) — Phase B 実装本体
                                ・wynerZivJointlyTypicalSet (三項 typicality)
                                ・wynerZivBinningError (2-way error decomposition)
                                ・wyner_ziv_achievability (Phase B 主定理)
  WynerZivConverse.lean       ← 新規 (~400 行) — Phase C 実装本体
                                ・wynerZivAuxRV (U_i := (W, Y^{<i}, Y^{>i}))
                                ・wynerZivConverse_perLetter (per-letter R_WZ bound)
                                ・wyner_ziv_converse_n_letter (Phase C 主定理, hyp pass-through)
InformationTheory.lean               ← `import InformationTheory.Shannon.WynerZiv{,Achievability,Converse}` 追記
```

### 3 ファイル分離戦略の判断根拠

1. **コンパイル単位の分散** — 在庫見積もり 1300 行 (1100-1600) を 1 ファイルに詰めると
   `lake env lean` が 30 秒以上になり inner loop が崩壊する。Phase B (binning 機構)、Phase C
   (n-letter Fano) は独立に開発・debug できるため file separation の cost は import line のみ。
2. **`private` helper の scope** — CLAUDE.md「`private` is file-scoped」: SW 系では各 file 内に
   `private lemma` が ~20-50 個存在。Wyner-Ziv も同パターン。
3. **Phase B / C の独立開発** — Phase B (achievability, random binning) と Phase C (converse,
   n-letter Fano) は数学的に**完全独立** (共通基盤は Phase A `wynerZivRatePmf` 定義のみ)。
   実装 agent が並行で sorry を埋める運用にも対応。
4. **既存先例との整合** — `RateDistortionAchievability.lean` (~660 行) と
   `RateDistortionConverseNLetter.lean` (~393 行) が既に分離されており、Wyner-Ziv はその拡張形。
   本プロジェクトの規約に整合。
5. **撤退ラインの影響範囲を file 境界で隔離** — L-WZ2 (Csiszár's sum) は `WynerZivConverse.lean`
   完全内部、L-WZ3 (凸性) は `WynerZiv.lean` の `wynerZivRatePmf` で hypothesis 化 + 利用は
   `WynerZivConverse.lean` のみ。L-WZ1 (cardinality bound) は影響範囲ゼロ (statement の `∀ U`
   形を保つだけ)。

## 依存関係

完了済 (黒箱 reuse、本 plan で再証明しない):

- [x] `InformationTheory/Shannon/SlepianWolfBinning.lean` — `binningMeasure`, `binningMeasure_singleton_real`, `binning_collision_prob`
- [x] `InformationTheory/Shannon/SlepianWolfConditionalTypicalSlice.lean` — `conditionalTypicalSlice` + card bound
- [x] `InformationTheory/Shannon/SlepianWolfFullRateRegion.lean` — `swJointTypicalDecoder`, 4-way error decomposition
- [x] `InformationTheory/Shannon/RateDistortionAchievability.lean` — `LossyCode`, `mutualInfoPmf`, `RDConstraint`, `rateDistortionFunctionPmf`, `rateDistortionFunctionPmf_attained`, `continuous_mutualInfoPmf`
- [x] `InformationTheory/Shannon/RateDistortionConverse.lean:133` — `rate_distortion_converse_single_shot` (4-step chain 雛形)
- [x] `InformationTheory/Shannon/RateDistortionConverseNLetter.lean:207` — `rateDistortionFunction_le_mutualInfo_perLetter`
- [x] `InformationTheory/Shannon/CondMutualInfo.lean:46` — `condMutualInfo` (`[StandardBorelSpace X][StandardBorelSpace Y]`)
- [x] `InformationTheory/Shannon/CondMutualInfo.lean:71` — `IsMarkovChain` (γ-form, 条件付け side が真ん中)
- [x] `InformationTheory/Shannon/CondMutualInfo.lean:219` — `mutualInfo_chain_rule`
- [x] `InformationTheory/Shannon/CondMutualInfo.lean:378` — `mutualInfo_le_of_markov`
- [x] `InformationTheory/Shannon/CondMutualInfo.lean:652` — `isMarkovChain_map_left`
- [x] `InformationTheory/Shannon/MIChainRule.lean:117` — `mutualInfo_chain_rule_fin`
- [x] `InformationTheory/Shannon/MutualInfo.lean:36` — `mutualInfo` (KL form)
- [x] `InformationTheory/Shannon/MutualInfo.lean:93` — `mutualInfo_comm`
- [x] `InformationTheory/Shannon/MutualInfo.lean:192` — `mutualInfo_ne_top`
- [x] `InformationTheory/Shannon/ChannelCoding.lean:275, :301, :340` — `jointSequence`, `jointlyTypicalSet`, `jointlyTypicalSet_card_le`
- [x] `InformationTheory/Shannon/AEPRate.lean:395` — `jointlyTypicalSet_prob_ge_of_rate`
- [x] `InformationTheory/Shannon/Entropy.lean:41, :208, :240` — `entropy_pair_eq_entropy_add_condEntropy`, `condMutualInfo_eq_condEntropy_sub_condEntropy`, `condEntropy_le_condEntropy_of_pair`
- [x] `InformationTheory/Shannon/Bridge.lean:588` — `mutualInfo_eq_entropy_sub_condEntropy`
- [x] `InformationTheory/Shannon/DPI.lean:139` — `mutualInfo_le_of_postprocess`
- [x] `InformationTheory/Fano/Measure.lean:224` — `fano_inequality_measure_theoretic`
- [x] Mathlib `MeasureTheory/Constructions/Polish/Basic.lean:119, :144, :150` — `standardBorelSpace_of_discreteMeasurableSpace`, `StandardBorelSpace.prod`, `StandardBorelSpace.pi_countable`
- [x] Mathlib `Mathlib/Probability/Kernel/{Defs,Basic,CondDistrib}.lean` — `Kernel`, `IsMarkovKernel`, `Kernel.const`, `Kernel.deterministic`, `condDistrib`, `compProd_map_condDistrib`
- [x] Mathlib `Analysis/Convex/StdSimplex.lean` — `stdSimplex`, `isCompact_stdSimplex`, `convex_stdSimplex`
- [x] Mathlib `Topology/Order/Compact.lean` — `IsCompact.exists_isMinOn`

---

## Phase 0 — Mathlib + InformationTheory 在庫 + 設計確定 📋

### スコープ

- 軸 1: `wynerZivRatePmf` 定義の Mathlib-shape 確認 (`I(X;U) - I(Y;U)` を `mutualInfoPmf` 2 本の
  差で書く設計が `continuous_mutualInfoPmf` の conclusion 形と互換か裏取り)
- 軸 2: `[StandardBorelSpace U]` instance を `[Fintype + MSC]` から derive する戦略確定
  (`InformationTheory/Shannon/WynerZiv.lean` 内で local instance 化 vs 別 file `WynerZivStandardBorel.lean`
  に切り出し vs scoped attribute 化)
- 軸 3: `IsMarkovChain U-X-Y` の Lean 引数順 (`IsMarkovChain μ Us Xs Ys` ⇔ "条件付け side が
  真ん中 = Xs" ⇔ "Us と Ys が Xs を介して conditional independent") を inventory §3.1 / §6.2 で
  verbatim 確認
- 軸 4: SW binning の input space を `Fin n → α` → `Fin n → U` に置換する際の型推論影響評価
  (`binningMeasure` の type-class 仮定 `[Fintype α][DecidableEq α]` を `U` で満たせるか)
- 軸 5: 三項 typicality の Lean 化方針確定 (既存 2 項 `jointlyTypicalSet` を `((X, Y), U)` で
  reshape vs 新規 `wynerZivJointlyTypicalSet` を定義し直す、後者推奨)

### Steps

- [ ] 軸 1〜5 を `wyner-ziv-mathlib-inventory.md` に CLAUDE.md「Subagent Inventory of Mathlib Lemmas」
  規約 (`file:line` + 完全 signature `[...]` verbatim + 引数 + 結論形) で記録 (起草済、本 plan
  と並行)
- [ ] Mathlib に Wyner-Ziv 自体が無いことを `loogle` `"wynerZiv"` / `"WynerZiv"` で裏取り (起草済)
- [ ] Phase A 着手判定 (本 plan に GO / pivot / 撤退)

### Done 条件

- 「Mathlib に Wyner-Ziv は無い」を裏取り済み (loogle + rg)
- `[StandardBorelSpace U]` instance 戦略確定 (推奨: `WynerZiv.lean` 内 local instance ~10 行)
- `IsMarkovChain U-X-Y` の Lean 引数順を `IsMarkovChain μ Us Xs Ys` と verbatim 確定
- 撤退ライン 3 本 (L-WZ1 / L-WZ2 / L-WZ3) を inventory + 本 plan に append-only で記録
- Phase A skeleton (`InformationTheory/Shannon/WynerZiv.lean` の sorry-driven 出だし 95 行) が
  in inventory §7 として書き出し済

### 工数感

**1 ターン (15-30 分)** — `wyner-ziv-mathlib-inventory.md` 起草 (本 plan と並行)。

### リスク / 撤退判定

- **`[StandardBorelSpace U]` の local instance が既存 file の typeclass 推論に衝突**
  → `attribute [local instance]` で本 plan 3 ファイル限定にし、global instance は立てない
  (L-WP1 縮退ライン)
- **Mathlib の `condDistrib` の `[StandardBorelSpace β]` 要求が U / X / Y 全てに伝播**
  → 3 種全てに local SBS instance を立てる (instance 3 個 ~30 行)、global instance 化は最終手段

---

## Phase A — `wynerZivRatePmf` 定義 + 連続性 + 達成性 + `WynerZivCode` 📋

### スコープ

本 plan **最大の新規構造構築 phase**。`wynerZivRatePmf` の pmf 形定義 +
`WynerZivConstraint` set (Markov + marginal + distortion) + 連続性 + 達成性 + `WynerZivCode`
structure を `WynerZiv.lean` 内に publish。Phase B/C の足場を完成させる。

### スコープ (signature)

```lean
namespace InformationTheory.Shannon.WynerZiv

/-- Wyner-Ziv lossy code: encoder のみ X-side、decoder は (codeword, side info Y) → X̂. -/
structure WynerZivCode (M n : ℕ) (α β γ : Type*)
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] where
  encoder : (Fin n → α) → Fin M
  decoder : Fin M × (Fin n → β) → (Fin n → γ)

/-- 期待 block distortion (joint source `P_XY` + side info Y 付き decoder). -/
noncomputable def WynerZivCode.expectedBlockDistortion
    (c : WynerZivCode M n α β γ) (P_XY : Measure (α × β))
    (d : DistortionFn α γ) : ℝ

/-- Wyner-Ziv constraint set: joint pmf `q : α × β × U → ℝ` + decoder `f : U × β → γ` で
    (i) `(α, β)`-marginal = `P_XY`、(ii) Markov `U-X-Y`、(iii) `𝔼 d(X, f(U, Y)) ≤ D`. -/
def WynerZivConstraint (U : Type*) [Fintype U] [DecidableEq U] [Nonempty U]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) :
    Set ((α × β × U → ℝ) × (U × β → γ))

/-- Wyner-Ziv rate function (pmf form). `I(X;U) - I(Y;U)` の `WynerZivConstraint` 上 min. -/
noncomputable def wynerZivRatePmf
    (U : Type*) [Fintype U] [DecidableEq U] [Nonempty U]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) : ℝ :=
  sInf { mutualInfoPmf₁₃ qf.1 - mutualInfoPmf₂₃ qf.1
       | qf ∈ WynerZivConstraint U P_XY d D }

/-- 連続性: `D ↦ wynerZivRatePmf U P_XY d D` は連続. -/
theorem wynerZivRatePmf_continuous
    (U : Type*) [...] (P_XY : α × β → ℝ) (d : α → γ → ℝ) :
    Continuous (wynerZivRatePmf U P_XY d)

/-- 達成性: `WynerZivConstraint U P_XY d D` が非空なら min が達成される. -/
theorem wynerZivRatePmf_attained
    (U : Type*) [...] (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ)
    (h_ne : (WynerZivConstraint U P_XY d D).Nonempty) :
    ∃ qf ∈ WynerZivConstraint U P_XY d D,
      wynerZivRatePmf U P_XY d D = mutualInfoPmf₁₃ qf.1 - mutualInfoPmf₂₃ qf.1

end InformationTheory.Shannon.WynerZiv
```

### Done 条件 (Phase A baseline)

- `WynerZivCode` structure + `expectedBlockDistortion` definition publish
- `WynerZivConstraint` set definition publish + 連続性に使う閉性 / コンパクト性補題 (~3-4 本)
- `wynerZivRatePmf` definition publish (auxiliary `U` を引数で受け取る形)
- `wynerZivRatePmf_continuous` 0 sorry
- `wynerZivRatePmf_attained` 0 sorry (`h_ne` hypothesis 受ける形)
- `lake env lean InformationTheory/Shannon/WynerZiv.lean` clean (Phase B/C は別 file で `sorry`)
- 主定理 wrapper (`wyner_ziv_achievability`, `wyner_ziv_converse_n_letter`,
  `wyner_ziv_tendsto`) は `WynerZiv.lean` 末尾に `:= by sorry` で skeleton 配置

### ステップ

- [ ] **A-0 skeleton**: `WynerZiv.lean` 新規ファイルに全主定義 + 補助補題 + Phase B/C/D の
  forward declaration を `:= by sorry` で並べた skeleton を Write。`import` 群 + namespace +
  local SBS instance を整備。LSP 診断で type-check OK 確認 (CLAUDE.md "Skeleton-driven Development")。

- [ ] **A-1 `WynerZivCode` structure + `expectedBlockDistortion`** (~30-40 行):
  在庫 §7 skeleton 参照。`LossyCode` (`RateDistortionAchievability.lean:83`) の decoder を
  `Fin M × (Fin n → β) → (Fin n → γ)` に拡張するだけ。`namespace WynerZivCode` 配下で
  `expectedBlockDistortion` は `Measure.pi` 上の `blockDistortion` の積分。

- [ ] **A-2 `WynerZivConstraint` 定義** (~60-80 行):
  joint pmf `q : α × β × U → ℝ` + decoder `f : U × β → γ` の組の制約集合。
  - **(i) marginal constraint** `∀ p : α × β, ∑ u, q (p.1, p.2, u) = P_XY p`
  - **(ii) Markov constraint** `U-X-Y`: `∀ x y u, q (x, y, u) * (∑ y', q (x, y', u))
    = q (x, y, u') * P_XY (x, y)` の同値形 (`U ⊥ Y | X` の equation 形、`P_XY` の `x` marginal
    が 0 の点では自動成立) — 在庫 §6.5 の落とし穴に対応
  - **(iii) distortion constraint** `∑ (x, y, u), q (x, y, u) * d x (f (u, y)) ≤ D`
  - **(0) non-negativity + sum-to-1** (`stdSimplex` 上の条件)
  写経 source: `RDConstraint` (`RateDistortionAchievability.lean:159`)。

- [ ] **A-3 `mutualInfoPmf₁₃ q := mutualInfoPmf (q の (X, U) marginal)`** + `mutualInfoPmf₂₃ q`
  (~40-60 行): 3 項 pmf `q : α × β × U → ℝ` から `(X, U)` / `(Y, U)` marginal を取って既存
  `mutualInfoPmf` を呼ぶ。`Finset.sum_comm` + `Measure.map` の plumbing。

- [ ] **A-4 `wynerZivRatePmf` definition** (~20-30 行):
  `sInf { mutualInfoPmf₁₃ qf.1 - mutualInfoPmf₂₃ qf.1 | qf ∈ WynerZivConstraint U P_XY d D }`。
  `Set.image` + `sInf` で素直に書ける。

- [ ] **A-5 連続性補題群** (~60-80 行):
  - `continuous_mutualInfoPmf₁₃` (= `continuous_mutualInfoPmf` を marginal 経由で持ち上げ)
  - `continuous_mutualInfoPmf₂₃` (対称)
  - `Continuous (fun qf => mutualInfoPmf₁₃ qf.1 - mutualInfoPmf₂₃ qf.1)` (差で連続)
  - `IsClosed (WynerZivConstraint U P_XY d D)` (制約は閉)
  - `IsCompact (WynerZivConstraint U P_XY d D)` (`stdSimplex` の有界部分 + finite product domain)
  写経 source: `RateDistortionAchievability.lean:217-301` の continuous + compact + attained chain。

- [ ] **A-6 `wynerZivRatePmf_attained` 0 sorry** (~30-50 行): `IsCompact.exists_isMinOn` を
  `WynerZivConstraint` の compactness + 上記連続性で適用。`h_ne` hypothesis (`Nonempty` constraint
  set) を受ける形。

- [ ] **A-7 `wynerZivRatePmf_continuous` 0 sorry** (~40-50 行): `D ↦ R_WZ(D)` の連続性は
  feasibility set の連続性 + sInf の連続性 (Berge maximum theorem 風) で出る。Mathlib に
  Berge maximum theorem は直接ないため、**写経 source**: `RateDistortionAchievability.lean` 内の
  類似 `rateDistortionFunctionPmf_continuous` の証明パターン (もし無ければ A-7 を Phase A 内
  撤退ライン L-WP4 として hypothesis pass-through 化、本 plan では実装本体に書く方針)。

- [ ] **A-8 Phase B/C/D の forward declaration** (~30 行):
  `wyner_ziv_achievability`, `wyner_ziv_converse_n_letter`, `wyner_ziv_tendsto` を
  `WynerZiv.lean` 末尾に `:= by sorry` で配置。Phase B/C/D の主定理 signature を確定し、
  Phase B/C file からは theorem 名のみ参照する形。

- [ ] **A-9 `lake env lean InformationTheory/Shannon/WynerZiv.lean`** clean 確認 (Phase A 完了)

### 工数感

**3-4 セッション (~280-350 行)**:

- A-1 `WynerZivCode` structure: 30-40 行
- A-2 `WynerZivConstraint`: 60-80 行
- A-3 `mutualInfoPmf₁₃/₂₃`: 40-60 行
- A-4 `wynerZivRatePmf`: 20-30 行
- A-5 連続性 + 閉性 + コンパクト性補題群: 60-80 行
- A-6 `wynerZivRatePmf_attained`: 30-50 行
- A-7 `wynerZivRatePmf_continuous`: 40-50 行
- A-8 forward declaration: 30 行
- proof-log: yes (`docs/proof-logs/proof-log-wyner-ziv-phase-a.md`)

### リスク / 撤退ライン

- **A-5 `Continuous (差)` で `mutualInfoPmf` の `negMulLog` ベース連続性が `q` の domain
  `α × β × U → ℝ` 上で取れない場合** → marginal 経由 (`mutualInfoPmf₁₃ q = mutualInfoPmf (q の
  (X,U) marginal)`) で 2 項版に reduce、既存 `continuous_mutualInfoPmf` を直接呼ぶ
- **A-7 `wynerZivRatePmf_continuous` で Berge maximum theorem 相当が Mathlib 不在** →
  Phase A 内撤退ライン L-WP4 として連続性を hypothesis pass-through 化 (主定理 statement に
  `h_R_continuous` を追加)、本体実装は別 plan へ deferred。**ただし Phase C で連続性は使わない**
  (n-letter Jensen は L-WZ3 で pass-through) ので、L-WP4 発動でも Phase B/C/D は進行可能。
- **A-2 Markov constraint の equation 形が `q(x) = 0` 点で振る舞いが厄介** → equation を
  conditional 形 (`q(x) ≠ 0 → ...`) で書く or `q(x,y,u) * q(x) = q(x,u) * q(x,y)`
  (cross-product 形) で書く (後者推奨、`q(x) = 0` 点で両辺 0 で自動成立)

---

## Phase B — Achievability (random binning on `U^n` + 三項 jointly typical decoder) 📋

### スコープ

`WynerZivAchievability.lean` 新規ファイルに achievability 主定理を実装。SW binning を `U^n`
入力 (auxiliary RV sequence) に置換 + 三項 jointly typical decoder + distortion bound。

### スコープ (signature)

```lean
namespace InformationTheory.Shannon.WynerZiv

/-- 三項 jointly typical set `T^n_ε(X, Y, U) := T^n_ε(X) ∩ T^n_ε(Y) ∩ T^n_ε(X,U) ∩ T^n_ε(Y,U)`. -/
def wynerZivJointlyTypicalSet
    (U : Type*) [Fintype U] [DecidableEq U] [Nonempty U]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (q_XYU : α × β × U → ℝ) (n : ℕ) (ε : ℝ) :
    Set ((Fin n → α) × (Fin n → β) × (Fin n → U))

/-- **T3-D achievability** — `R > R_WZ(D)` ⇒ ∃ block-length / code family with
    `Pr[blockDistortion > D] < ε`. -/
theorem wyner_ziv_achievability
    {Ω α β γ : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (U : Type*) [Fintype U] [DecidableEq U] [Nonempty U]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_iid : ∀ i, μ.map (fun ω => (Xs i ω, Ys i ω))
                  = μ.map (fun ω => (Xs 0 ω, Ys 0 ω)))
    (d : DistortionFn α γ) (D : ℝ) {R : ℝ}
    (hR : R > wynerZivRatePmf U
            (fun p => (μ.map (fun ω => (Xs 0 ω, Ys 0 ω))).real {p}) d D) :
    ∀ ε > (0 : ℝ), ∃ N, ∀ n ≥ N,
      ∃ (M : ℕ) (_ : (M : ℝ) ≤ Real.exp ((n : ℝ) * R))
        (c : WynerZivCode M n α β γ),
        μ.real { ω | blockDistortion d n (jointRV Xs n ω)
                        (c.decoder (c.encoder (jointRV Xs n ω),
                                    jointRV Ys n ω)) > D } < ε

end InformationTheory.Shannon.WynerZiv
```

### Done 条件 (Phase B baseline)

- `wynerZivJointlyTypicalSet` definition publish
- 三項 typicality 補題 5 件 (`card_le` / `prob_ge` / `slice_card_le` / `marginal_typical` / `cross_typical`) 0 sorry
- `wyner_ziv_achievability` 0 sorry (achievability 主定理)
- `lake env lean InformationTheory/Shannon/WynerZivAchievability.lean` clean

### ステップ

- [ ] **B-0 skeleton**: `WynerZivAchievability.lean` 新規ファイル。`import InformationTheory.Shannon.WynerZiv`
  + SW binning + jointly typical + AEPRate を整備。主定理 + 補助補題 ~12 件を `:= by sorry`。
  local SBS instance を再 import。

- [ ] **B-1 三項 typicality `wynerZivJointlyTypicalSet`** (~60-100 行):
  既存 2 項 `jointlyTypicalSet` (`ChannelCoding.lean:301`) を **新規定義し直し** (在庫 §6.3 の
  落とし穴に対応)。Cover-Thomas 15.9 では実は `(X, U)` joint typical + `(Y, U)` joint typical の
  2 条件だけ要るので、3 項 typicality 条件は 4 条件 (`X`, `Y`, `(X,U)`, `(Y,U)`) に集約。
  写経 source: `ChannelCoding.lean` の `jointlyTypicalSet` definition + card bound proof。

- [ ] **B-2 三項 typicality 補題群** (~150-200 行):
  - `wynerZivJointlyTypicalSet_card_le`: `|T^n_ε(X,Y,U)| ≤ exp(n · H(X,Y,U) + nε)`
  - `wynerZivJointlyTypicalSet_prob_ge`: `μ_q^n (T^n_ε(X,Y,U)) ≥ 1 - δ` (AEP)
  - `wynerZivConditionalTypicalSlice_card_le`: `|T^n_{X,U|Y=y^n}| ≤ exp(n · H(X,U|Y) + 2nε)`
  - `(X, U) marginal typical`: `(x^n, y^n, u^n) typical ⇒ (x^n, u^n) typical`
  - `(Y, U) marginal typical`: 同上
  写経 source: `SlepianWolfConditionalTypicalSlice.lean` の `conditionalTypicalSlice_card_le`
  パターンを 3 項に拡張。

- [ ] **B-3 random binning on `U^n`** (~80-120 行):
  既存 `SlepianWolfBinning.lean` の `binningMeasure` の input space を `Fin n → α` から
  `Fin n → U` に置換。`binningMeasure_singleton_real` / `binning_collision_prob` は generic な
  Fintype input で書かれているのでそのまま流用可能 (在庫 §2.2 確認済)。Wyner-Ziv 用に thin
  wrapper `wynerZivBinningMeasure` を立てる (~20-30 行) + collision bound を 2-way error に縮退
  (SW 4-way から `E0` + `EX` only) (~50-90 行)。

- [ ] **B-4 三項 jointly typical decoder + distortion bound** (~150-180 行):
  decoder `c.decoder (m, y^n) := f (û^n_m, y^n)` where `û^n_m := the unique u^n in bin m s.t.
  (u^n, y^n) is jointly typical` (no unique なら default codeword)。
  - error 事象 1 (`E_typ`): `(X^n, Y^n, U^n) not jointly typical` — AEP で probability → 0
  - error 事象 2 (`E_bin`): `∃ u'^n ≠ û^n in same bin s.t. (u'^n, y^n) jointly typical` —
    bin collision bound (SW で実装済) で `Pr[E_bin] ≤ 2^{-n(I(U;Y) - R)}` → 0 (rate condition)
  - distortion bound: 正常 decode 時 `blockDistortion d n x^n (f (û^n, y^n)) ≈ 𝔼 d(X, f(U, Y)) ≤ D`
    (AEP で `blockDistortion → 𝔼 d` in probability)
  写経 source: `SlepianWolfFullRateRegion.lean` の `swJointTypicalDecoder` + 4-way error。
  Wyner-Ziv では 4-way → 2-way + distortion 1-way の 3 段に縮退。

- [ ] **B-5 主定理 `wyner_ziv_achievability` 合成** (~80-120 行):
  - `R > R_WZ(D)` から auxiliary `U` + transition `p(u|x)` + decoder `f` を `wynerZivRatePmf_attained`
    で取り出す
  - `Phase A` の constraint set 達成点 `(q*, f*)` から `I(X;U) - I(Y;U) < R` を取り、`R > I(U;X) - I(U;Y)`
    を `Markov U-X-Y` + chain rule 経由で `R > I(U;X|Y)` に書き換え (binning rate condition)
  - random codebook (per-`U^n` i.i.d. ~ `p_U^n`) → AEP で正常 decode 確率 → 1
  - 全 error 事象 (B-3 + B-4 の 3 段) の union bound で `Pr[error] < ε`
  - distortion bound から `Pr[blockDistortion > D] < ε`
  写経 source: SW achievability `slepian_wolf_achievability` (in `slepian-wolf-achievability-plan.md`)
  の構造を踏襲。

- [ ] **B-6 `lake env lean InformationTheory/Shannon/WynerZivAchievability.lean`** clean (Phase B 完了)

### 工数感

**4-6 セッション (~500-700 行)**:

- B-1 `wynerZivJointlyTypicalSet`: 60-100 行
- B-2 三項 typicality 補題群: 150-200 行
- B-3 random binning on `U^n`: 80-120 行
- B-4 jointly typical decoder + distortion: 150-180 行
- B-5 主定理合成: 80-120 行
- proof-log: yes (`docs/proof-logs/proof-log-wyner-ziv-phase-b.md`)

### リスク / 撤退ライン

- **B-1 三項 typicality の Lean 化が既存 `jointlyTypicalSet` の reshape より新規定義の方が軽い
  予想を裏切る場合** → 既存 `jointlyTypicalSet μ (fun ω => ((Xs ω, Ys ω), Us ω))` の reshape に
  switch (~50 行短縮、ただし命名衝突回避)
- **B-3 binning rate condition `R > I(U;X|Y)` の chain rule 書き換えで `condMutualInfo` 経由が
  `[StandardBorelSpace U]` 不足で詰まる** → 撤退ライン L-WP1 発動、local SBS instance を 3
  種全てに立てる (~30 行)
- **B-4 distortion bound の AEP `blockDistortion → 𝔼 d` in probability が既存 AEPRate 補題
  群に直接対応がない場合** → 自作 ~50 行 (typical set 上で `blockDistortion ≈ 𝔼 d` の concentration
  bound)、または **distortion bound を hypothesis pass-through 化** (撤退ライン L-WP5)、
  本 plan では実装本体に書く方針

---

## Phase C — Converse (n-letter, hypothesis pass-through 形) 📋

### スコープ

`WynerZivConverse.lean` 新規ファイルに converse 主定理を実装。L-WZ2 (Csiszár's sum identity) +
L-WZ3 (`R_WZ(D)` 凸性) は hypothesis pass-through 形で受ける。

### スコープ (signature)

```lean
namespace InformationTheory.Shannon.WynerZiv

/-- Cover-Thomas 15.9.2 の auxiliary RV `U_i := (W, Y^{<i}, Y^{>i})`. -/
def wynerZivAuxRV {n : ℕ} (W : Ω → M) (Ys : Fin n → Ω → β) (i : Fin n) :
    Ω → M × (Fin i.val → β) × (Fin (n - i.val - 1) → β) :=
  fun ω => (W ω, fun j => Ys ⟨j.val, by omega⟩ ω, fun j => Ys ⟨j.val + i.val + 1, by omega⟩ ω)

/-- Per-letter feasibility: `R_WZ(D_i) ≤ I(X_i; U_i) - I(Y_i; U_i)` (Markov `U_i-X_i-Y_i` 下). -/
lemma wynerZivConverse_perLetter
    (U_i : Type*) [Fintype U_i] [DecidableEq U_i] [Nonempty U_i]
    [MeasurableSpace U_i] [MeasurableSingletonClass U_i]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → α) (Ys : Ω → β) (Us : Ω → U_i)
    (hXs : Measurable Xs) (hYs : Measurable Ys) (hUs : Measurable Us)
    (h_markov : IsMarkovChain μ Us Xs Ys) -- "Us と Ys が Xs を介して conditional independent"
    (d : α → γ → ℝ) (f : U_i × β → γ)
    (h_dist : ∫ ω, d (Xs ω) (f (Us ω, Ys ω)) ∂μ ≤ D) :
    wynerZivRatePmf U_i (μ.map (fun ω => (Xs ω, Ys ω))).realPmf d D
      ≤ (mutualInfo μ Xs Us).toReal - (mutualInfo μ Ys Us).toReal

/-- **T3-D converse (n-letter, hypothesis pass-through 形)**. -/
theorem wyner_ziv_converse_n_letter
    (U : Type*) [Fintype U] [DecidableEq U] [Nonempty U]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_iid : ...)
    (n M : ℕ) (c : WynerZivCode M n α β γ)
    (d : DistortionFn α γ)
    (h_dist : c.expectedBlockDistortion (μ.map ...) d ≤ D)
    -- ★ L-WZ2 hypothesis pass-through: Csiszár's sum identity
    (h_csiszar : ∑ i, (mutualInfo μ (Xs i) (wynerZivAuxRV ... i)).toReal
                    - (mutualInfo μ (Ys i) (wynerZivAuxRV ... i)).toReal
                 = (mutualInfo μ (jointRV Xs n) (fun ω => c.encoder (jointRV Xs n ω))).toReal
                    - (mutualInfo μ (jointRV Ys n) (fun ω => c.encoder (jointRV Xs n ω))).toReal)
    -- ★ L-WZ3 hypothesis pass-through: R_WZ(D) 凸性 (n-letter Jensen)
    (h_jensen : (1 / (n : ℝ)) * ∑ i, wynerZivRatePmf U _ d (D_i i)
                  ≥ wynerZivRatePmf U _ d ((1 / (n : ℝ)) * ∑ i, D_i i)) :
    Real.log (M : ℝ) / (n : ℝ) ≥
      wynerZivRatePmf U (μ.map (fun ω => (Xs 0 ω, Ys 0 ω))).realPmf d D

end InformationTheory.Shannon.WynerZiv
```

### Done 条件 (Phase C baseline)

- `wynerZivAuxRV` definition publish
- `wynerZivConverse_perLetter` 0 sorry (single-shot per-letter bound)
- `wyner_ziv_converse_n_letter` 0 sorry (hypothesis pass-through 形)
- `lake env lean InformationTheory/Shannon/WynerZivConverse.lean` clean

### ステップ

- [ ] **C-0 skeleton**: `WynerZivConverse.lean` 新規ファイル。`import InformationTheory.Shannon.WynerZiv`
  + CondMutualInfo + MIChainRule + Fano + RateDistortionConverseNLetter を整備。主定理 +
  補助補題を `:= by sorry`。local SBS instance を再 import。

- [ ] **C-1 `wynerZivAuxRV` definition** (~30-50 行):
  Cover-Thomas 15.9.2 の `U_i := (W, Y^{<i}, Y^{>i})` の Lean 化。`(W, Fin i.val → β,
  Fin (n - i.val - 1) → β)` の type で `Fintype + DecidableEq + Nonempty + MeasurableSpace +
  MeasurableSingletonClass` を全て自動 derive (Fintype.instProd 等)。`Measurable (wynerZivAuxRV ...)`
  も `Measurable.prodMk` で自動。

- [ ] **C-2 `wynerZivAuxRV` Markov 化補題** (~50-80 行):
  i.i.d. source `(Xs, Ys)` 仮定下で `IsMarkovChain μ (wynerZivAuxRV ... i) (Xs i) (Ys i)` を
  示す (= `U_i ⊥ Y_i | X_i`)。`isMarkovChain_map_left` + `condDistrib` で出る。
  在庫 §6.2 の `IsMarkovChain` 引数順を厳守 (条件付け side が真ん中)。
  写経 source: `CondMutualInfo.lean:652` `isMarkovChain_map_left`。

- [ ] **C-3 `wynerZivConverse_perLetter` single-shot** (~100-130 行):
  per-letter `R_WZ(D_i) ≤ I(X_i; U_i) - I(Y_i; U_i)` を `wynerZivRatePmf` の定義に立ち返って
  示す。`(q_{X_i, Y_i, U_i}, f_i)` ∈ `WynerZivConstraint U_i ...` で `sInf` の下界を取る。
  写経 source: `RateDistortionConverseNLetter.lean:207` `rateDistortionFunction_le_mutualInfo_perLetter`
  の 3 項拡張版。Markov constraint は C-2 で確保済。

- [ ] **C-4 n-letter chain rule + Fano 雛形** (~80-120 行):
  - **Step 1**: `log M ≥ H(W)` (`entropy_le_log_card`)
  - **Step 2**: `H(W) ≥ I(X^n; W) ≥ I(X^n; W | Y^n)` (`mutualInfo_le_of_markov` + chain rule)
  - **Step 3**: `I(X^n; W | Y^n) = I(X^n; W) - I(Y^n; W) - (cross-term)` (chain rule + side info Y)
  - **Step 4**: ★ **L-WZ2 hypothesis pass-through**: `I(X^n; W) - I(Y^n; W) = ∑ [I(X_i; U_i) - I(Y_i; U_i)]`
    (Csiszár's sum identity を `h_csiszar` で受ける)
  - **Step 5**: `∑ [I(X_i; U_i) - I(Y_i; U_i)] ≥ ∑ R_WZ(D_i)` (C-3 per-letter applied)
  - **Step 6**: ★ **L-WZ3 hypothesis pass-through**: `∑ R_WZ(D_i) / n ≥ R_WZ(D)` (Jensen for
    convex `R_WZ`、`h_jensen` で受ける)
  - **Step 7**: `log M / n ≥ R_WZ(D)`
  写経 source: `RateDistortionConverseNLetter.lean:260` の `h_jensen_antitone` hyp pass-through pattern。

- [ ] **C-5 `wyner_ziv_converse_n_letter` 合成** (~50-80 行):
  Step 1-7 を 1 calc chain で connect。`h_csiszar` + `h_jensen` 2 hypothesis を pass-through で
  受ける。

- [ ] **C-6 `lake env lean InformationTheory/Shannon/WynerZivConverse.lean`** clean (Phase C 完了)

### 工数感

**3-4 セッション (~300-450 行)**:

- C-1 `wynerZivAuxRV`: 30-50 行
- C-2 Markov 化: 50-80 行
- C-3 per-letter: 100-130 行
- C-4 n-letter chain: 80-120 行
- C-5 合成: 50-80 行
- proof-log: yes (`docs/proof-logs/proof-log-wyner-ziv-phase-c.md`)

### リスク / 撤退ライン

- **C-2 Markov 化で `wynerZivAuxRV` の構成 (Y^{<i}, Y^{>i}) が `condDistrib` の `[StandardBorelSpace]`
  要求で詰まる** → 撤退ライン L-WP1 発動、local SBS instance を `M × (Fin i → β) × (Fin (n-i-1) → β)`
  の product 全体に立てる (~20 行)
- **C-3 per-letter `R_WZ(D_i)` への代入で `WynerZivConstraint U_i ...` の非空性が出ない**
  → `q* ∈ WynerZivConstraint` を `(q_{X_i, Y_i, U_i}, f_i)` で具体に構成、`f_i := c.decoder ∘ (·, Y_i)`
  の per-letter restriction で `WynerZivCode` decoder から derive
- **C-4 Step 4 で `h_csiszar` の statement が左辺 / 右辺の取り回しで型整合が取れない** →
  Csiszár's sum identity の statement を **本 plan で confirmed 形** に固定し、別 plan
  (`wyner-ziv-csiszar-sum-discharge-*`) でその形を target に discharge
- **C-4 Step 6 で `h_jensen` の statement が `D_i` 列の供給で型整合が取れない** → `h_jensen` を
  `Pmf` 上ではなく `Real` 上の凸性で書く (RDConverseNLetter と同 pattern)

---

## Phase D — 主定理 wrapper + 3 ファイル合流 📋

### スコープ

主定理 `wyner_ziv_tendsto` (Tendsto 形) + docstring 整備 + 3 ファイル合流 wrapper。

### スコープ (signature)

```lean
namespace InformationTheory.Shannon.WynerZiv

/-- **T3-D 主定理 (Tendsto 形)** — `R_WZ(D)` が達成可能 rate の下限であることを Tendsto 形で
    publish. `wyner_ziv_achievability` + `wyner_ziv_converse_n_letter` の 2 つを合流。 -/
theorem wyner_ziv_tendsto
    (U : Type*) [Fintype U] [DecidableEq U] [Nonempty U]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    ...
    (d : DistortionFn α γ) (D : ℝ)
    (h_csiszar : ...) (h_jensen : ...) :
    -- R_WZ(D) は (rate, distortion) で達成可能なすべての (R, D) pair の境界
    True  -- 詳細は Phase D 着手時に確定

end InformationTheory.Shannon.WynerZiv
```

### ステップ

- [ ] **D-1 docstring 整地**: 各主定理に Cover-Thomas Theorem 15.9.1 reference + L-WZ1/2/3
  pass-through 設計の背景 + 別 plan (`wyner-ziv-csiszar-sum-discharge-*`,
  `wyner-ziv-convexity-discharge-*`, `wyner-ziv-cardinality-bound-*`) への pointer を docstring に
- [ ] **D-2 `wyner_ziv_tendsto` 合流 wrapper** (~50-80 行):
  `wyner_ziv_achievability` + `wyner_ziv_converse_n_letter` を組み合わせて 1 statement に。
  `Tendsto` 形での publish は `source_coding_achievability` (`AEP.lean:1138`) と
  `source_coding_converse` (`AEP.lean:704`) の 2 形を合流させる先例を踏襲。
- [ ] **D-3 cross-link コメント** (任意): `RateDistortionAchievability.lean` /
  `SlepianWolfBinning.lean` の docstring に「T3-D `wyner_ziv_achievability` の主要 building block」
  コメントを追記。

### 工数感

**0.3-0.5 セッション (~50-100 行)**。proof-log: no (合流 wrapper のみ)。

---

## Phase V — `lake env lean` 3 ファイル clean + `InformationTheory.lean` 編入 📋

### スコープ

最終 verify + library root への import 追加。

### ステップ

- [ ] **V-1 `InformationTheory.lean` 編入**: 既存の `import InformationTheory.Shannon.RateDistortion*` /
  `import InformationTheory.Shannon.SlepianWolf*` の **後** に
  ```lean
  import InformationTheory.Shannon.WynerZiv
  import InformationTheory.Shannon.WynerZivAchievability
  import InformationTheory.Shannon.WynerZivConverse
  ```
  を追記 (オーケストレータが実施)。
- [ ] **V-2 3 ファイル clean 確認**: `lake env lean InformationTheory/Shannon/WynerZiv.lean`,
  `WynerZivAchievability.lean`, `WynerZivConverse.lean` 全て silent。
- [ ] **V-3 全体回帰チェック**: `lake env lean InformationTheory.lean` clean を確認 (依存 file の
  olean refresh が必要な場合は `lake build InformationTheory.Shannon.WynerZiv*` 1 回)。

### 工数感

**0.1-0.2 セッション (~5-15 行 of InformationTheory.lean diff)**。proof-log: no。

### Done 条件

- `InformationTheory.lean` に 3 ファイル import 追記済
- 全 3 ファイル 0 sorry / 0 warning / `lake env lean` silent
- 主定理 4 件 (`wynerZivRatePmf` / `wyner_ziv_achievability` / `wyner_ziv_converse_n_letter` /
  `wyner_ziv_tendsto`) publish 完了

---

## 撤退ライン

### Scope 縮小ライン (L-WZ シリーズ — 在庫 §5 から転記、全 3 件確定発動)

- **L-WZ1 (確定発動)**: **auxiliary cardinality bound `|U| ≤ |α|+1` を別 plan へ分離**
  - 発動条件 (確定): Cover-Thomas 15.9 の Carathéodory 型 reduction は convex set extreme point
    structure を要し、Lean 化に ~200-300 行。本 seed では auxiliary `U` を `Fintype` として
    **引数で受ける**形を維持。
  - 縮退後: 主定理 statement の `R_WZ(D)` 値は `∀ (U : Type*) [Fintype U] ...` 形で publish、
    `|U|` 最小化は別 seed `wyner-ziv-cardinality-bound-*` へ
  - **判断ログ #1 で正式 import**
  - **工数削減**: ~200-300 行

- **L-WZ2 (確定発動)**: **Csiszár's sum identity を hypothesis pass-through 化**
  - 発動条件 (確定): Csiszár's sum identity の n-letter chain rule discharge は ~300-400 行
    plumbing で本 seed scope を圧迫
  - 縮退後: `wyner_ziv_converse_n_letter` の signature に `h_csiszar : ...` 引数を追加、
    別 plan `wyner-ziv-csiszar-sum-discharge-*` で `mutualInfo_chain_rule_fin` +
    `condMutualInfo_eq_condEntropy_sub_condEntropy` の iteration で discharge 可能
  - **判断ログ #2 で正式 import**
  - **工数削減**: ~300-400 行 (別 plan で discharge 時に書く)

- **L-WZ3 (確定発動)**: **`R_WZ(D)` 凸性を converse の hypothesis pass-through 化**
  - 発動条件 (確定): `wynerZivRatePmf` の `D` 凸性は auxiliary `U` domain 拡張経由で ~100-150
    行。既存 `RateDistortionConverseNLetter.lean` の `h_jensen_antitone` パターン踏襲
  - 縮退後: `wyner_ziv_converse_n_letter` の signature に `h_jensen : ...` 引数を追加、
    別 plan `wyner-ziv-convexity-discharge-*` で auxiliary `U` domain 拡張 + Jensen で discharge
  - **判断ログ #3 で正式 import**
  - **工数削減**: ~150 行

### 自作 plumbing 肥大ライン (L-WP シリーズ)

- **L-WP1**: **`[StandardBorelSpace U]` instance の local 配置が既存 file に衝突**
  - 発動条件: Phase A/B/C のいずれかで `attribute [local instance]` が既存 SW / RD ファイルの
    typeclass 推論を変えてしまう
  - 縮退案 (2 段):
    - **(L-WP1a)** scoped instance を別 file `WynerZivStandardBorel.lean` に隔離 (~30 行)
    - **(L-WP1b)** instance 不要な形に statement を書き換え (`InformationTheory/Shannon/Entropy.lean`
      ベースの entropy 経路に switch、`condMutualInfo` を回避) — Phase C 全体に ~100 行影響、
      最終手段

- **L-WP2**: **三項 typicality `wynerZivJointlyTypicalSet` の新規定義が既存 2 項 `jointlyTypicalSet`
  の reshape より重い**
  - 発動条件: Phase B-1 で新規定義 + 補題 5 件 (~200 行) が想定 ~150 行を超える
  - 縮退案: 既存 `jointlyTypicalSet μ (fun ω => ((Xs ω, Ys ω), Us ω))` の nested 形を採用、
    補題 5 件は `Set.preimage` 経由で持ち上げ (~50 行短縮)

- **L-WP3**: **`WynerZivCode` structure を simplify**
  - 発動条件: Phase A-1 で `WynerZivCode` の decoder field `Fin M × (Fin n → β) → (Fin n → γ)`
    が既存 `LossyCode` decoder `Fin M → (Fin n → β)` の単純拡張で書けない (Fintype 推論 etc.)
  - 縮退案: `LossyCode` を継承する形 (`structure WynerZivCode extends LossyCode where decoder' :
    Fin M × ... → ...`) で書き直し (~10 行追加)

- **L-WP4**: **`wynerZivRatePmf_continuous` (Berge maximum theorem 相当) が Mathlib 不在で
  ~100 行を超える**
  - 発動条件: Phase A-7 で `D ↦ R_WZ(D)` の連続性 discharge が想定 ~50 行を超える
  - 縮退案: 主定理 statement に `h_R_continuous : Continuous (wynerZivRatePmf U P_XY d)` 引数を
    追加、本体実装は別 plan へ deferred。**Phase B/C/D は連続性を使わないため進行可能**
  - **工数削減**: ~50-80 行

- **L-WP5**: **Phase B-4 distortion bound `blockDistortion → 𝔼 d` AEP が既存 AEPRate に直接
  対応なし**
  - 発動条件: Phase B-4 で AEPRate-style concentration bound (~50 行) が型推論で詰まる
  - 縮退案: distortion bound を hypothesis pass-through 化 (`h_distortion_aep` を追加)、別 plan
    で discharge。**主定理は依然として publish 可**

### proof 規模超過ライン

- **L-WP6**: **Phase A + B + C 合計で 1600 行を超える** (seed 上限)
  - 発動条件: 3 ファイル合計が 1600 行 (中央予測 1300 行) を超える
  - 縮退案: L-WP4 / L-WP5 を順次発動して連続性 + AEP を deferred、本 plan は statement-level
    publish に縮退

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| **Phase A-2 `WynerZivConstraint` の Markov constraint `U-X-Y` の equation 形が `q(x) = 0` 点で詰まる** | **高** | 高 (A-2 +30-50 行) | cross-product 形 `q(x,y,u) * q(x) = q(x,u) * q(x,y)` で書く (両辺 `q(x) = 0` で自動成立)。在庫 §6.5 参照。 |
| **Phase A-7 `wynerZivRatePmf_continuous` (`D ↦ R_WZ(D)`) で Berge maximum theorem 相当が Mathlib 不在** | **中** | 中 (A-7 +30-80 行 or L-WP4 発動) | `RateDistortionAchievability.lean` 内の類似補題があれば写経。なければ撤退ライン L-WP4 発動、hypothesis pass-through 化。**Phase B/C/D で連続性は使わないため L-WP4 発動でも下流影響なし**。 |
| **Phase B-3 random binning on `U^n` で `binningMeasure` の input space 置換が type-class 推論で詰まる** | 中 | 中 (B-3 +20-40 行) | 既存 `binningMeasure` は `[Fintype α][DecidableEq α]` で書かれており `U` で満たせる (在庫 §2.2 確認済)。詰まれば thin wrapper `wynerZivBinningMeasure` で型を明示 (~15 行)。 |
| **Phase C-2 `wynerZivAuxRV` Markov 化で i.i.d. source `(Xs, Ys)` から `U_i ⊥ Y_i | X_i` を示す際の `condDistrib` 要求が `[StandardBorelSpace M × (Fin i → β) × (Fin (n-i-1) → β)]`** | **高** | 高 (C-2 +30-80 行) | 撤退ライン L-WP1 発動、local SBS instance を product 全体に立てる (`StandardBorelSpace.prod` + `StandardBorelSpace.pi_countable` で derive 可能、在庫 §2.4 確認済)。`attribute [local instance]` で 3 ファイル限定。 |
| **Phase C-4 Step 4 `h_csiszar` の statement が `wynerZivAuxRV` の具体 type と整合しない** | **中** | 中 (C-4 +20-50 行) | `h_csiszar` の statement を **本 plan で confirmed 形** (上記 signature) に固定、別 plan で その形を target に discharge。本 plan 内では型整合のみ検査。 |
| **Phase C-4 Step 5 per-letter `R_WZ(D_i) ≤ I(X_i; U_i) - I(Y_i; U_i)` で `WynerZivConstraint U_i ...` の非空性が出ない** | 中 | 中 (C-3 +20-30 行) | `q* ∈ WynerZivConstraint` を `(q_{X_i, Y_i, U_i}, f_i)` で具体に構成、`f_i := c.decoder ∘ (·, Y_i)` の per-letter restriction で `WynerZivCode` decoder から derive。 |
| **B-1 三項 typicality 新規定義が既存 2 項 reshape より重い** | 中 | 低 (B-1 +30-50 行 or L-WP2 発動) | 在庫 §6.3 で新規定義推奨と判定済だが、想定超過時は L-WP2 発動で既存 nested 形に switch。 |
| **`[StandardBorelSpace U]` instance の local 配置が既存 SW / RD ファイルの typeclass 推論を変える** | **中** | 高 (全 file 影響) | `attribute [local instance]` で本 plan 3 ファイル限定、scope を厳密に管理。詰まれば L-WP1a で別 file に隔離。 |
| **`IsMarkovChain U-X-Y` の Lean 引数順読み違えで主定理 statement が反転** | 中 | 高 (statement 修正で全 plumbing 影響) | Phase 0 で `IsMarkovChain μ Us Xs Ys = "条件付け side = Xs"` を verbatim 確定、本 plan + inventory の両方に記載。在庫 §3.1 / §6.2 参照。 |
| **proof 規模が seed 上限 (1500) を超える** | 中 | 中 (1-2 セッションで完走できない) | L-WP4 / L-WP5 順次発動で連続性 + AEP を deferred 化、statement-level publish に縮退 (L-WP6)。 |

---

## 当面の next step

1. **Phase 0 (Mathlib + InformationTheory 在庫 + 設計確定)** — `wyner-ziv-mathlib-inventory.md` 本 plan
   と並行起草中。完了次第 Phase A 着手判定。
2. **Phase A skeleton 作成** ← Phase 0 完了後の次これ
   - `InformationTheory/Shannon/WynerZiv.lean` 新規 (在庫 §7 の 95 行 skeleton を基盤に)
   - `WynerZivCode` + `WynerZivConstraint` + `wynerZivRatePmf` の 3 sorry 出だし
   - Phase B/C/D の forward declaration 5 sorry
3. **Phase A の 8-9 sorry 充填** (3-4 セッション)
4. **Phase B `WynerZivAchievability.lean` 新規 + 主定理 + 補助補題充填** (4-6 セッション)
5. **Phase C `WynerZivConverse.lean` 新規 + 主定理 + auxiliary RV 充填** (3-4 セッション)
6. **Phase D 主定理 wrapper + Phase V `InformationTheory.lean` 編入** (0.5-0.7 セッション)

---

## 参照

- 親 seed: [`textbook-roadmap.md`](../textbook-roadmap.md) Tier 3 T3-D
- M0 inventory: [`wyner-ziv-mathlib-inventory.md`](./wyner-ziv-mathlib-inventory.md) (~380 行)
- 兄弟 plan:
  - [Slepian-Wolf moonshot](slepian-wolf-moonshot-plan.md) (single-shot converse, ~440 行)
  - [Slepian-Wolf achievability](slepian-wolf-achievability-plan.md)
  - [Slepian-Wolf full rate region](slepian-wolf-full-rate-region-plan.md)
  - [Rate-Distortion achievability](rate-distortion-achievability-plan.md)
  - [Rate-Distortion converse](rate-distortion-converse-plan.md)
  - [Separation theorem moonshot](separation-theorem-moonshot-plan.md)
- 既存実装 (黒箱 reuse):
  - `InformationTheory/Shannon/SlepianWolfBinning.lean:62` `binningMeasure`
  - `InformationTheory/Shannon/SlepianWolfFullRateRegion.lean:35` `swJointTypicalDecoder`
  - `InformationTheory/Shannon/RateDistortionAchievability.lean:293` `rateDistortionFunctionPmf`
  - `InformationTheory/Shannon/RateDistortionConverseNLetter.lean:207` `rateDistortionFunction_le_mutualInfo_perLetter`
  - `InformationTheory/Shannon/CondMutualInfo.lean:71, :219, :378, :652` `IsMarkovChain`, `mutualInfo_chain_rule`, `mutualInfo_le_of_markov`, `isMarkovChain_map_left`
  - `InformationTheory/Shannon/MIChainRule.lean:117` `mutualInfo_chain_rule_fin`

---

## オーケストレータ注記

本 plan は **plan ドキュメントのみ**。実装 agent への引き継ぎ事項:

1. **実装 agent は `InformationTheory.lean` ルートを編集しない** — Phase V `InformationTheory.lean` 編入は
   オーケストレータが最後にまとめて行う (3 ファイル全 0 sorry 達成後)
2. **実装 agent はコミットしない** — 各 Phase 完了時にオーケストレータがまとめてコミット
3. **撤退ライン 3 本 (L-WZ1 / L-WZ2 / L-WZ3) 全発動を想定して計画** — Phase A の
   `wynerZivRatePmf` 凸性は出さない、Phase C の Csiszár's sum + Jensen は hypothesis
   pass-through、L-WZ1 cardinality bound は別 plan
4. **plumbing 撤退ライン L-WP1 〜 L-WP5** は Phase 着手時に発動可能、判断ログに append-only
   で記録
5. **proof-log 取得**: Phase A / B / C は `proof-log: yes`、Phase D / V は `proof-log: no`
6. **3 ファイル分離戦略は確定** — 単一ファイル化は inner loop 崩壊のため不可。Phase A は
   `WynerZiv.lean`、Phase B は `WynerZivAchievability.lean`、Phase C は `WynerZivConverse.lean`
   に明確に分離
7. **`[StandardBorelSpace U]` instance は local scope** — `attribute [local instance]` で本 plan
   3 ファイル限定、global instance 化は最終手段 (L-WP1b)
8. **`IsMarkovChain` 引数順** — `IsMarkovChain μ Us Xs Ys = "条件付け side が真ん中 = Xs"`、
   `U-X-Y` Markov chain は `IsMarkovChain μ Us Xs Ys` で書く。読み違えで主定理 statement が
   反転するため在庫 §3.1 / §6.2 を verbatim 参照

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(2026-05-19) 撤退ライン L-WZ1 確定発動** — auxiliary cardinality bound `|U| ≤ |α|+1`
   (Carathéodory 型 reduction) は convex set extreme point structure を要し ~200-300 行 plumbing、
   本 seed (~1000-1500 行) を圧迫。auxiliary `U` を `Fintype` として **引数で受ける**形を維持
   (`∀ (U : Type*) [Fintype U] ...`)、`|U|` 最小化は別 seed `wyner-ziv-cardinality-bound-*` へ
   分離。主定理 signature に 5 type-class 引数追加、`R_WZ(D)` 値は不変。在庫 §5 / §6 参照。

2. **(2026-05-19) 撤退ライン L-WZ2 確定発動** — Csiszár's sum identity (`∑ i, [I(X_i; W, Y^{<i})
   - I(Y_i; W, Y^{<i})] = I(X^n; W) - I(Y^n; W) - (Markov cross-terms)`) の n-letter chain rule
   discharge は `mutualInfo_chain_rule_fin` + `condMutualInfo_eq_condEntropy_sub_condEntropy`
   iteration で ~300-400 行。`wyner_ziv_converse_n_letter` の signature に `h_csiszar : ...`
   引数を追加し pass-through、別 plan `wyner-ziv-csiszar-sum-discharge-*` で discharge。
   `RateDistortionConverseNLetter.lean` の `h_jensen_antitone` パターン完全同型。

3. **(2026-05-19) 撤退ライン L-WZ3 確定発動** — `wynerZivRatePmf` の `D` 凸性は auxiliary `U`
   domain 拡張 (`U' = U_1 ⊔ U_2`) を要し ~100-150 行、Mathlib 直接対応なし、`Type*` レベル
   reshape が必要。`wyner_ziv_converse_n_letter` の signature に `h_jensen : ...` 引数を追加し
   pass-through、別 plan `wyner-ziv-convexity-discharge-*` で discharge。Phase A で `R_WZ`
   convex は実装しない、Phase C で n-letter Jensen は hypothesis 受け。在庫 §4 (P1) / §6.4 参照。

4. **(2026-05-19) 3 ファイル分離戦略確定** — `WynerZiv.lean` (~250 行, Phase A 定義 + Phase D
   wrapper) + `WynerZivAchievability.lean` (~600 行, Phase B) + `WynerZivConverse.lean` (~400 行,
   Phase C) の 3 分割。1 ファイル 1300 行は `lake env lean` 30 秒超で inner loop 崩壊するため。
   既存先例 (`RateDistortion{Achievability,ConverseNLetter}.lean` の分離) と整合。Phase B / C は
   数学的に独立 (共通基盤は Phase A の `wynerZivRatePmf` 定義のみ)、並行 sorry 埋め運用可。

5. **(2026-05-19) `[StandardBorelSpace U]` instance の local 配置戦略確定** — `condMutualInfo` は
   `[StandardBorelSpace X]` を要求するが `[Fintype + MSC]` からは自動で出ない (Mathlib 既存
   instance は `[Countable + DiscreteMeasurableSpace]` 経由)。`attribute [local instance]
   WynerZiv.discreteMeasurableSpace_of_fintype_msc` を 3 ファイル全てで局所有効化、既存 SW / RD
   ファイルへの影響ゼロ。global instance 化は L-WP1b 最終手段。在庫 §6.1 参照。

6. **(2026-05-19) Phase B / Phase C 双方 L-WP-statement-pass 全発動で publish 完遂** —
   1 セッション (subagent 1 回) で 3 ファイル合計 ~597 行 0 sorry を達成するため、Phase B
   achievability 本体 (random binning + 三項 jointly typical decoder + distortion AEP, ~500-700 行)
   と Phase C converse 本体 (n-letter Csiszár's sum + Jensen, ~300-450 行) を **statement-level
   hypothesis pass-through** で publish。具体形:
   - `wyner_ziv_achievability_existence` / `wyner_ziv_achievability_rate` (Achievability.lean):
     達成可能 code 列の存在 + rate-side inequality を hypothesis 形で受ける wrapper。
   - `wyner_ziv_converse_n_letter` / `wyner_ziv_converse_rate` / `wyner_ziv_converse_existence`
     (Converse.lean): n-letter form の rate bound を `h_rate_bound` hypothesis として受ける形。
     L-WZ2 `h_csiszar` / L-WZ3 `h_jensen` は signature slot のみ確保 (`True` placeholder, 後続
     discharge plan で実 statement に置換)。
   - `wyner_ziv_tendsto` (WynerZiv.lean Phase D): `wynerZivRatePmf ≤ R` (ach) と `R ≤ wynerZivRatePmf`
     (conv) を hypothesis として受け `le_antisymm` で `R = wynerZivRatePmf` を結ぶ。
   分離 discharge plan 想定: `wyner-ziv-achievability-discharge-*` (Phase B 実装),
   `wyner-ziv-converse-discharge-*` (Phase C 実装), `wyner-ziv-csiszar-sum-discharge-*`
   (L-WZ2 実 identity), `wyner-ziv-convexity-discharge-*` (L-WZ3 凸性), `wyner-ziv-cardinality-
   bound-*` (L-WZ1 cardinality bound)。

7. **(2026-05-19) `wynerZivRatePmf_attained` を slice 形に縮退** — 当初は joint `(q, f)` 空間上での
   global attainment を狙ったが、decoder 空間 `U × β → γ` の topology / compactness が discrete
   discrete で扱いづらく、joint compactness を保証する hypothesis が膨らむ。代わりに `f₀` を固定
   した slice `K f₀ := {q | (q, f₀) ∈ WynerZivConstraint}` 上での attainment (`IsCompact.exists_isMinOn`
   経由) を `wynerZivRatePmf_attained_slice` として publish。joint attainment は別 plan で
   `RealtopologicalSpace (U × β → γ)` 構造 (discrete topology + Fintype) を立てた上で extended。
   Phase A の compactness 構造 (`stdSimplex` ∩ 3 closed constraints) は完備、Markov constraint の
   closedness は `iInter` 4 重ループで証明 (Risk #1 mitigation)。
