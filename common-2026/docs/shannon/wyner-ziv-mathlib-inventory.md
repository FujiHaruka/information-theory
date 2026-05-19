# Wyner–Ziv: Mathlib API 在庫調査 (T3-D Phase 0)

> **Parent**: T3-D Wyner-Ziv (Cover-Thomas Ch.15.9 ; `docs/textbook-roadmap.md` §Tier 3)
>
> **Status (2026-05-19):** 起草。loogle index (`.lake/build/loogle.index`) + Mathlib /
> Common2026 直 `rg` で本定理の Lean 化に必要な 7 軸 (R_WZ 定義 / auxiliary RV / Markov chain /
> conditional joint typicality / chain rule (with side info) / SW binning 流用 / RD 流用) を
> 機械的に確認。各候補補題は **CLAUDE.md「Subagent Inventory of Mathlib Lemmas」** に従って
> 位置 / 完全シグネチャ ([..] 型クラス verbatim) / 引数 / 結論形 を記録する。
>
> **本ファイルは在庫のみ**: 計画 / 実装は別 plan (`docs/shannon/wyner-ziv-moonshot-plan.md`,
> `Common2026/Shannon/WynerZiv*.lean`) で別途立てる。

## サマリ (一行)

Phase achievability + converse のうち、**既存 Common2026 / Mathlib で実体が既にある API は
推定 65%**（特に MI / condMI / DPI / SlepianWolf binning + jointly typical decoder / RD pmf 形
+ n-letter Jensen が完備）、**自作必要なのは 8 件**（うち 5 件は SW + RD plumbing の流用で
低リスク、3 件 — auxiliary RV `U` の random kernel measure / `R_WZ(D)` の `Real` 形定義 + 凸性 /
auxiliary cardinality bound — は Wyner-Ziv 固有の新規工数）。**撤退ライン候補 3 本** (L-WZ1
auxiliary cardinality bound defer / L-WZ2 converse の auxiliary 形 publish (single-letterization
defer) / L-WZ3 凸性 hypothesis pass-through)。

## 1. 主定理の最終形 (再掲)

### 目標 (Cover-Thomas Theorem 15.9.1)

side info `Y` at decoder only で source `X` を distortion `D` 以下で再現する rate

```
R_WZ(D) = min_{p(u | x)} min_{f : U × Y → X̂} [ I(X ; U) − I(Y ; U) ]
```

ただし min は (i) auxiliary RV `U` (Markov chain `U − X − Y` を満たす) の transition
`p(u | x)`、(ii) reconstruction map `f : U × Y → X̂` を回す。distortion constraint
`𝔼 d(X, f(U, Y)) ≤ D` 下。

### Lean 風 signature (achievability + converse)

```lean
-- ① rate function 定義
noncomputable def wynerZivRate
    {α β γ : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (P_XY : α × β → ℝ)  -- joint source pmf
    (d : α → γ → ℝ)
    (D : ℝ) : ℝ
  -- := sInf { I(X;U) - I(Y;U) over pmf q on (α×β×U) + decoder f : U×β → γ
  --   s.t. (X,Y)-marginal = P_XY, Markov U─X─Y, 𝔼 d(X, f(U,Y)) ≤ D }

-- ② achievability
theorem wynerZiv_achievability
    [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
      [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β]
      [MeasurableSingletonClass β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ] [MeasurableSpace γ]
      [MeasurableSingletonClass γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_iid : ∀ i, μ.map (fun ω => (Xs i ω, Ys i ω))
                  = μ.map (fun ω => (Xs 0 ω, Ys 0 ω)))
    (d : α → γ → ℝ) (D : ℝ) {R : ℝ}
    (hR : R > wynerZivRate (μ.map (fun ω => (Xs 0 ω, Ys 0 ω))).realPmf d D) :
    ∃ N, ∀ n ≥ N, ∃ (M : ℕ) (_ : (M : ℝ) ≤ Real.exp ((n : ℝ) * R))
      (enc : (Fin n → α) → Fin M) (dec : Fin M × (Fin n → β) → (Fin n → γ)),
      μ.real { ω | blockDistortion d n (jointRV Xs n ω)
                      (dec (enc (jointRV Xs n ω), jointRV Ys n ω)) > D } ≤ ε

-- ③ converse (single-shot 形、hypothesis pass-through 許容)
theorem wynerZiv_converse_single_shot
    [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
      [MeasurableSingletonClass α]
    [Fintype β] ... [Fintype γ] ...
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → α) (Ys : Ω → β)
    (encoder : α → M) (decoder : M × β → γ)
    -- distortion + rate hypotheses
    ...
    -- Cover-Thomas 15.9 form (auxiliary U の存在 hypothesis pass-through)
    (h_aux : ∃ (U : Type*) (_ : Fintype U) (Us : Ω → U) ..., ... ) :
    Real.log M ≥ wynerZivRate (μ.map ...) d D
```

### 想定証明戦略 (pseudo-Lean, ~12 行)

```
-- Achievability (Phase B):
-- 1. random codebook on `U`: i.i.d. draws from p_U^n (induced from p(u|x) marginal)
-- 2. encoder = jointly-typical bin index of (x^n, u^n) (Slepian-Wolf binning 流用)
-- 3. decoder = f(u^n_decoded, y^n)
-- 4. error events: E_typ ∪ E_codeword ∪ E_bin; each → 0 by AEPRate

-- Converse (Phase C, hypothesis pass-through):
-- 1. Fano + chain rule with side info `Y`:
--      n·R ≥ I(X^n ; W) ≥ I(X^n ; W | Y^n)   -- conditioning ≥ when Y indep prior
-- 2. n-letter chain rule (per-letter U_i := (W, Y^{i-1}, Y^n_{≠i})):
--      I(X^n ; W | Y^n) = ∑ I(X_i ; U_i) - I(Y_i ; U_i)
--   (Csiszár's sum identity, hypothesis pass-through)
-- 3. Single-letterize via R_WZ(D) ≤ I(X_i ; U_i) - I(Y_i ; U_i) at D_i
-- 4. Jensen on R_WZ convexity → R ≥ R_WZ(D)
```

## 2. API 在庫テーブル (カテゴリごと)

### 2.1 既存 Common2026 — そのまま流用可

| 概念 | API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| 相互情報量 `I(X;Y)` (KL form) | `mutualInfo` | `Common2026/Shannon/MutualInfo.lean:36` | ✅ 完備 | Phase A `I(X;U) - I(Y;U)` の RHS 両項を直接書ける |
| MI 対称性 | `mutualInfo_comm` | `Common2026/Shannon/MutualInfo.lean:93` | ✅ | Phase B / C で頻出 |
| MI 有限性 | `mutualInfo_ne_top` | `Common2026/Shannon/MutualInfo.lean:192` | ✅ (`[Fintype X][Fintype Y]`) | Phase C 全段 (`ENNReal.toReal_mono`) |
| 条件付き MI `I(X;Y\|Z)` | `condMutualInfo` | `Common2026/Shannon/CondMutualInfo.lean:46` | ✅ (`[StandardBorelSpace X][StandardBorelSpace Y]`) | Phase C converse の n-letter chain rule に必須 |
| 2 変数 MI chain rule | `mutualInfo_chain_rule` | `Common2026/Shannon/CondMutualInfo.lean:219` | ✅ | Csiszár's sum identity の 2 変数 base |
| n 変数 MI chain rule | `mutualInfo_chain_rule_fin` | `Common2026/Shannon/MIChainRule.lean:117` | ✅ (Fintype α `Fin n → α`) | Phase C n-letter converse |
| Markov chain `X → Z → Y` (γ-form) | `IsMarkovChain` | `Common2026/Shannon/CondMutualInfo.lean:71` | ✅ | `U − X − Y` 制約の Lean 化に直接対応 |
| Markov ⇒ MI bound | `mutualInfo_le_of_markov` | `Common2026/Shannon/CondMutualInfo.lean:378` | ✅ | DPI: `I(X;U) ≤ I(X;Z)` 形 |
| Markov post-processing | `isMarkovChain_map_left` | `Common2026/Shannon/CondMutualInfo.lean:652` | ✅ | Phase A auxiliary RV `U = f(X)` の Markov 化 |
| DPI (post-processing) | `mutualInfo_le_of_postprocess` | `Common2026/Shannon/DPI.lean:139` | ✅ | Phase C `I(W;X̂) ≤ I(W;X)` |
| MI ↔ entropy 橋 | `mutualInfo_eq_entropy_sub_condEntropy` | `Common2026/Shannon/Bridge.lean:588` | ✅ | Phase C `I(X;U) - I(Y;U)` 展開 |
| 3 項 entropy 橋 | `mutualInfo_eq_entropy_add_entropy_sub_jointEntropy` | `Common2026/Shannon/MIChainRule.lean:449` | ✅ | optional, single-letterization 簡略形 |
| 条件付き entropy chain | `entropy_pair_eq_entropy_add_condEntropy` | `Common2026/Shannon/Entropy.lean:41` | ✅ (`[Fintype X][Fintype Y]`) | `H(X^n,U^n) = H(X^n) + H(U^n\|X^n)` |
| conditioning ≤ | `condEntropy_le_condEntropy_of_pair` | `Common2026/Shannon/Entropy.lean:240` | ✅ | Phase C side info 単調性 |
| condMI ≤ → condMI 橋 | `condMutualInfo_eq_condEntropy_sub_condEntropy` | `Common2026/Shannon/Entropy.lean:208` | ✅ | converse の Real 化 |
| 条件付き entropy | `MeasureFano.condEntropy` | `Common2026/Fano/Measure.lean:68` | ✅ | textbook 式と直接対応 |
| Fano 不等式 (side info paired form) | `fano_inequality_measure_theoretic` | `Common2026/Fano/Measure.lean:224` | ✅ (`Yo := (Y, sideinfo)` で paired) | Phase C `H(X^n \| dec, Y^n) ≤ n·δ(ε)` |
| `entropy_le_log_card` | `entropy_le_log_card` (in `MaxEntropy` namespace) | `Common2026/Shannon/SlepianWolf.lean:45` (and re-exposed `MaxEntropy.entropy_le_log_card`) | ✅ | Phase C `log M ≥ H(W)` |

### 2.2 既存 Common2026 — Slepian–Wolf binning + jointly typical (Wyner-Ziv で再利用)

| 概念 | API | file:line | 状態 | Wyner-Ziv での扱い |
|---|---|---|---|---|
| Random binning measure | `binningMeasure` | `Common2026/Shannon/SlepianWolfBinning.lean:62` | ✅ | Phase B auxiliary `U^n` 上の bin index に流用 (input space を `Fin n → U` に置換) |
| Binning collision (singleton mass) | `binningMeasure_singleton_real` | `Common2026/Shannon/SlepianWolfBinning.lean:78` | ✅ | Phase B 誤り bound 計算 |
| Binning collision prob | `binning_collision_prob` | `Common2026/Shannon/SlepianWolfBinning.lean` (~150) | ✅ | Phase B `Pr[same bin] = 1/M` |
| Joint sequence | `ChannelCoding.jointSequence` | `Common2026/Shannon/ChannelCoding.lean:275` | ✅ | Phase B 三項 typicality `(X^n, Y^n, U^n)` を `((X,Y), U)` でネスト |
| Joint typical set | `ChannelCoding.jointlyTypicalSet` | `Common2026/Shannon/ChannelCoding.lean:301` | ✅ (二項 `α × β`) | Phase B `T^n_{ε}(X, Y, U)` を `((X,Y), U)` reshape で構築 |
| Conditional typical slice | `ChannelCoding.conditionalTypicalSlice` | `Common2026/Shannon/SlepianWolfConditionalTypicalSlice.lean:59` | ✅ | Phase B `\|T_{X\|Y}^n(y)\| ≤ exp(n(H(X\|Y)+2ε))` を `(U\|Y)` に流用 |
| Joint typical set card bound | `jointlyTypicalSet_card_le` | `Common2026/Shannon/ChannelCoding.lean:340` | ✅ | Phase B 誤り bound |
| Joint typical set prob → 1 | (in `AEPRate.lean`) `jointlyTypicalSet_prob_ge_of_rate` | `Common2026/Shannon/AEPRate.lean:395` | ✅ | Phase B AEP 経由 |
| Joint typical decoder (SW form) | `swJointTypicalDecoder` | `Common2026/Shannon/SlepianWolfFullRateRegion.lean:35` | ✅ | Phase B side info Y 入り decoder に reshape (`decoder : Fin M × (Fin n → β) → (Fin n → α)`) |
| 4-way error event decomposition | `swError_E0/EX/EY/EXY` | `Common2026/Shannon/SlepianWolfFullRateRegion.lean:51-83` | ✅ | Wyner-Ziv では **2-way 縮退** (E_typ + E_bin only)。SW 4-way の `EX` (= bin collision on `U^n`) と `E0` (= joint not typical) を回す |

### 2.3 既存 Common2026 — Rate-Distortion (Wyner-Ziv で再利用)

| 概念 | API | file:line | 状態 | Wyner-Ziv での扱い |
|---|---|---|---|---|
| Distortion function `α → γ → NNReal` | `DistortionFn` | `Common2026/Shannon/RateDistortionAchievability.lean:59` | ✅ | そのまま流用 |
| Block distortion `(1/n)∑ d(x_i, y_i)` | `blockDistortion` | `Common2026/Shannon/RateDistortionAchievability.lean:62` | ✅ | そのまま流用 |
| Lossy code structure | `LossyCode` | `Common2026/Shannon/RateDistortionAchievability.lean:83` | ✅ (decoder `Fin M → Fin n → β`) | Wyner-Ziv では decoder を `Fin M × (Fin n → β) → Fin n → γ` に拡張 — 新規 structure `WynerZivCode` を立てる (~10 行) |
| Expected block distortion | `LossyCode.expectedBlockDistortion` | `Common2026/Shannon/RateDistortionAchievability.lean:93` | ✅ | 同上、side info 引数を追加 |
| `R(D)` pmf 形 | `rateDistortionFunctionPmf` | `Common2026/Shannon/RateDistortionAchievability.lean:293` | ✅ (`negMulLog` 連続) | **流用不可** — `R_WZ(D)` は MI 差 `I(X;U) − I(Y;U)` で auxiliary `U` を回す min が要る。**新規定義** `wynerZivRatePmf` (~50 行) |
| `R(D)` 達成性 (compactness) | `rateDistortionFunctionPmf_attained` | `Common2026/Shannon/RateDistortionAchievability.lean:301` | ✅ | Phase A `wynerZivRatePmf` の min 達成性に同形式の戦略 (compact constraint + continuous obj) |
| Per-letter feasibility | `rateDistortionFunction_le_mutualInfo_perLetter` | `Common2026/Shannon/RateDistortionConverseNLetter.lean:207` | ✅ | Phase C per-letter `R_WZ(D_i) ≤ I(X_i; U_i) - I(Y_i; U_i)` |
| n-letter Jensen + antitone | (hypothesis pass-through in) `rate_distortion_converse_n_letter_singleLetter` | `Common2026/Shannon/RateDistortionConverseNLetter.lean:260` | ✅ | Phase C 同パターンで `R_WZ` も hypothesis pass-through 採用 (L-WZ3 撤退ライン) |
| Single-shot RD converse | `rate_distortion_converse_single_shot` | `Common2026/Shannon/RateDistortionConverse.lean:133` | ✅ | Phase C 骨格 — 4 step chain (entropy → MI → DPI → R(D̃)) は Wyner-Ziv でも同型 |
| RD pmf convexity | `RDConstraint_convex` | `Common2026/Shannon/RateDistortionAchievability.lean:217` | ✅ | Phase A `wynerZivRatePmf` 凸性は **新規証明** が必要 (auxiliary `U` domain mixing は別 strategy) |
| RD pmf MI 連続 | `continuous_mutualInfoPmf` | `Common2026/Shannon/RateDistortionAchievability.lean:267` | ✅ | Phase A `wynerZivRatePmf` の連続性証明に流用 (但し `I(X;U) − I(Y;U)` は **連続だが凸ではない**) |

### 2.4 Mathlib — Kernel / condDistrib (auxiliary RV の Lean 化)

| 概念 | API | file:line | 状態 | Wyner-Ziv での扱い |
|---|---|---|---|---|
| Kernel structure | `ProbabilityTheory.Kernel` | `Mathlib/Probability/Kernel/Defs.lean:55` | ✅ | auxiliary RV `U` の transition `p(u\|x)` を `Kernel α U` で表現 |
| Markov kernel class | `IsMarkovKernel` | `Mathlib/Probability/Kernel/Defs.lean:147` | ✅ | `p(u\|x)` が確率測度 |
| Constant kernel | `Kernel.const` | `Mathlib/Probability/Kernel/Basic.lean:178` | ✅ | trivial auxiliary `U ⊥ (X,Y)` |
| Deterministic kernel | `Kernel.deterministic` | `Mathlib/Probability/Kernel/Basic.lean:~55` | ✅ | `U = f(X)` 形 |
| `condDistrib Y X μ` | `ProbabilityTheory.condDistrib` | `Mathlib/Probability/Kernel/CondDistrib.lean` (definition) | ✅ (`[StandardBorelSpace β]`) | `condDistrib Us Xs μ : Kernel α U` で `p(u\|x)` を構成 |
| compProd ↔ condDistrib | `ProbabilityTheory.compProd_map_condDistrib` | `Mathlib/Probability/Kernel/CondDistrib.lean:82` | ✅ | `μ.map (X, U) = (μ.map X) ⊗ₘ condDistrib U X μ` |
| condDistrib uniqueness | `condDistrib_ae_eq_of_measure_eq_compProd` | `Mathlib/Probability/Kernel/CondDistrib.lean:163` | ✅ (`[IsFiniteKernel κ]`) | Phase A `U` の transition 同定 |
| Kernel compProd | `ProbabilityTheory.Kernel.compProd` | `Mathlib/Probability/Kernel/Composition/CompProd.lean` | ✅ | Phase A joint `(X, U, Y)` の構成 |
| Markov kernel of deterministic | `isMarkovKernel_deterministic` | `Mathlib/Probability/Kernel/Basic.lean:81` | ✅ | `U = f(X)` |
| KL invariant under measurable equiv | `klDiv_map_measurableEquiv` | `Common2026/Shannon/MutualInfo.lean:52` | ✅ | (Common2026 自作) Phase A `U ≃ U'` reshape |
| KL chain rule | `klDiv_compProd_eq_add` | `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:204` | ✅ | Phase C `I((Z,X);Y) = I(Z;Y) + I(X;Y\|Z)` |
| Standard Borel for countable + discrete | `standardBorelSpace_of_discreteMeasurableSpace` | `Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:119` | ✅ (`[Countable α][DiscreteMeasurableSpace α]`) | **重要**: Fintype + MeasurableSingletonClass は直接 SBS を与えない。auxiliary `U` が Fintype の場合、`DiscreteMeasurableSpace U` instance を確保する必要あり (危険箇所 §9 参照) |
| Standard Borel prod | `StandardBorelSpace.prod` | `Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:144` | ✅ | `(X × U)` |
| Standard Borel pi (countable) | `StandardBorelSpace.pi_countable` | `Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:150` | ✅ (`[Countable ι]`) | `Fin n → U` の SBS |

### 2.5 Mathlib — その他基盤

| 概念 | API | file:line | 状態 | Wyner-Ziv での扱い |
|---|---|---|---|---|
| Product measure `μ.prod ν` | `MeasureTheory.Measure.prod` | `Mathlib/MeasureTheory/Measure/Prod.lean` | ✅ | Phase B i.i.d. codebook |
| `Measure.map_prod_map` | `MeasureTheory.Measure.map_prod_map` | `Mathlib/MeasureTheory/Measure/Prod.lean:825` | ✅ | Phase B/C reshape |
| `Measurable.prodMk` | `Measurable.prodMk` | `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean` (core) | ✅ | paired RV 全般 |
| `Fintype.card_prod` | `Fintype.card_prod` | `Mathlib/Data/Fintype/Prod.lean` | ✅ | `Fintype.card (α × β) = α·β` |
| Convex on simplex | `stdSimplex`, `isCompact_stdSimplex`, `convex_stdSimplex` | `Mathlib/Analysis/Convex/StdSimplex.lean` | ✅ | Phase A `R_WZ(D)` 達成性 + 凸性 (但し auxiliary `U` 上の simplex は **dimensional augmentation** が要、§9 参照) |
| `Real.negMulLog` 連続 | `Real.continuous_negMulLog` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean` | ✅ | Phase A `wynerZivRatePmf` 連続性 |
| `Real.concaveOn_negMulLog` | `Real.concaveOn_negMulLog` | (同上) | ✅ | Jensen plumbing |
| `ConcaveOn.le_map_sum` | `ConcaveOn.le_map_sum` | `Mathlib/Analysis/Convex/Jensen.lean` | ✅ | n-way Jensen (auxiliary domain `U`) |
| `IsCompact.exists_isMinOn` | `IsCompact.exists_isMinOn` | `Mathlib/Topology/Order/Compact.lean` | ✅ | Phase A min 達成性 |

## 3. 主要前提条件ボックス (型クラス事故の起きやすい lemma)

以下は **`[...]` 型クラス前提を見落とすと主定理 statement が引きずられる lemma 群**。Wyner-Ziv
で頻出する 4 件を列挙：

### 3.1 `condMutualInfo` (`Common2026/Shannon/CondMutualInfo.lean:46`)

```lean
noncomputable def condMutualInfo
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) : ℝ≥0∞
```

- **要 `[StandardBorelSpace X]` + `[StandardBorelSpace Y]`** — 第 1, 2 引数。
- **`Z` には SBS 不要** (条件付け側 = `μ.map Zc` 上の積分の base measure only)。
- **`Ω` には SBS 不要** — γ-form 採用済 (CLAUDE.md `Mathlib-shape-driven Definitions` 指針)。
- Wyner-Ziv では `U`, `X`, `Y` 全てに `[Fintype + DecidableEq + MeasurableSingletonClass]` を
  仮定するため、**`StandardBorelSpace` instance を自力で確保する必要あり** (§9 危険箇所)。

### 3.2 `mutualInfo_chain_rule` (`Common2026/Shannon/CondMutualInfo.lean:219`)

```lean
theorem mutualInfo_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc) :
    mutualInfo μ (fun ω => (Zc ω, Xs ω)) Yo
      = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc
```

- `[IsProbabilityMeasure μ]` (NOT `IsFiniteMeasure`) — `condDistrib` の Markov kernel
  property を要する。Wyner-Ziv では問題なし (i.i.d. source は probability measure)。
- `Z` 側に **SBS 不要** — 条件付け side のみ。**X / Y には SBS 必須**。

### 3.3 `mutualInfo_chain_rule_fin` (`Common2026/Shannon/MIChainRule.lean:117`)

```lean
theorem mutualInfo_chain_rule_fin
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (Yo : Ω → Y) (hYo : Measurable Yo) :
    mutualInfo μ (fun ω i => Xs i ω) Yo
      = ∑ i : Fin n, condMutualInfo μ (Xs i) Yo
          (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
```

- **`α` (first chain) は Fintype + MeasurableSingletonClass + Nonempty** (`section ChainRuleFin`
  variable 宣言)。X 側に SBS 不要 (Fintype で derive される MeasurableEq で十分)。
- **`Y` には SBS 必須** — condMI 経由。
- Wyner-Ziv で `Y_i` 側に chain rule を当てる際にこの auxiliary direction を逆にしておく必要が
  あるかもしれない (Csiszár's sum identity の n-letter 展開、§9 危険箇所)。

### 3.4 `rate_distortion_converse_single_shot` (`Common2026/Shannon/RateDistortionConverse.lean:133`)

```lean
theorem rate_distortion_converse_single_shot
    [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β]
    {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (encoder : α → M) (decoder : M → β)
    (hX : Measurable X)
    (hencoder : Measurable encoder) (hdecoder : Measurable decoder)
    (d : α → β → ℝ)
    (hd : Measurable (fun p : α × β => d p.1 p.2))
    (hMI_W_finite : mutualInfo μ X (fun ω => encoder (X ω)) ≠ ∞) :
    (rateDistortionFunction d (μ.map X)
        (∫ ω, d (X ω) (decoder (encoder (X ω))) ∂μ)).toReal
      ≤ Real.log (Fintype.card M)
```

- **`α` には完全 Fintype セット**、**`β` には MeasurableSingletonClass のみ** (`Fintype β` 不要)。
  Wyner-Ziv 復号側 `γ` も同様に MSC のみで OK。
- **`M` (rate label) 側に完全 Fintype セット必須**。
- **`hMI_W_finite` hypothesis pass-through あり** — Wyner-Ziv でも同型で受ける。

## 4. 自作が必要な要素

優先度順、実装推奨、工数感、落とし穴を併記：

### P0 (高優先 — Phase A の核)

#### (a) `wynerZivRatePmf` — `R_WZ(D)` の pmf 形定義

- **目的**: Cover-Thomas 15.9 の `R_WZ(D) := min_{p(u|x)} min_{f} [I(X;U) - I(Y;U)]` を Lean 化。
- **推奨**: **auxiliary alphabet `U` を `Fintype + DecidableEq + Nonempty` で受ける** (引数として
  受け取り、Carathéodory 型 `|U| ≤ |α| + 1` bound は L-WZ1 に defer)。
  pmf domain は `(α × β × U) → ℝ` (joint pmf) + decoder `f : U × β → γ`。
  ```lean
  noncomputable def wynerZivRatePmf
      (U : Type*) [Fintype U] [DecidableEq U] [Nonempty U]
      (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) : ℝ :=
    sInf { mutualInfoPmf₃_marg₁₃ q - mutualInfoPmf₃_marg₂₃ q
         | (q : α × β × U → ℝ) ×' (f : U × β → γ) // ...
              -- (α,β) marginal = P_XY
              -- Markov U-X-Y (q(x,y,u) = q(x,u) * P_XY(x,y) / P_X(x))
              -- expected distortion ≤ D }
  ```
  ただし `Real.negMulLog` ベースの 3 項版 MI helper (`mutualInfoPmf₃_*`) は **新規** (~80 行)。
- **工数感**: ~120-180 行 (definition + non-emptyness + sInf 達成性 + 連続性)。
- **落とし穴**:
  - `RateDistortionAchievability.lean` の `mutualInfoPmf` は **2 項版**。3 項 pmf 上の
    `I(X;U), I(Y;U)` を別々に計算する関数を 2 本新規に書く必要あり。
  - auxiliary `U` の選び方を **引数で受ける** か **`Type*` 上で existential** にするかで
    statement の汎用性が変わる (existential なら `∃ U, |U| ≤ N ∧ ...` 形になり、L-WZ1 で
    cardinality bound を分離可能)。

#### (b) `R_WZ(D)` 連続性 + 凸性 + 達成性

- **目的**: Phase A 既存 RD インフラ (`continuous_mutualInfoPmf` + `IsCompact.exists_isMinOn`) を
  auxiliary `U` 上の constraint に拡張。
- **推奨**: `wynerZivRateConstraintPmf` を `(α × β × U → ℝ)` 上の `stdSimplex` 部分集合として
  定義 → `IsClosed + IsCompact` → `Continuous (... - ...)` → `exists_isMinOn`。
  凸性は **Mathlib に直接対応する補題なし** (`I(X;U) - I(Y;U)` は **U domain で凸ではなく
  concave**)。Cover-Thomas は `U` の domain 拡張 (convex hull) 経由で凸化するが、本 Lean 化
  では **L-WZ3 で凸性を hypothesis pass-through** とする。
- **工数感**: ~150-200 行 (constraint set 3 種 + 連続性 + 達成性 + L-WZ3 凸性 hyp)。
- **落とし穴**:
  - `I(X;U) - I(Y;U)` の差は連続だが **負の値を取り得る** (Markov chain `U-X-Y` 下では非負)。
    Lean 値域を `ℝ` (not `ℝ≥0`) で取る必要あり。
  - Markov constraint `U-X-Y` を `stdSimplex` 上の閉条件として書ける形にする (`q(x,y,u) =
    q(x,u) * q(x,y) / q(x)` の equation を connected components 上で確認、`q(x) = 0` 区域では
    自動成立) — **新規 ~50 行**。

### P1 (Phase B achievability の核)

#### (c) `WynerZivCode` structure

- **目的**: `LossyCode` の decoder を side info 入りに拡張。
- **推奨**:
  ```lean
  structure WynerZivCode (M n : ℕ) (α β γ : Type*)
      [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] where
    encoder : (Fin n → α) → Fin M
    decoder : Fin M × (Fin n → β) → (Fin n → γ)
  ```
- **工数感**: ~20-30 行 (structure + `expectedBlockDistortion_sideinfo` + 非負性)。
- **落とし穴**: 既存 `LossyCode` と naming conflict 回避。`namespace InformationTheory.Shannon.WynerZiv`
  を立てる。

#### (d) Auxiliary RV `U_i := (W, Y^{i-1}, Y^n_{≠i})` (Cover-Thomas 15.9.2 converse trick)

- **目的**: Phase C n-letter converse で per-letter `I(X_i; U_i) - I(Y_i; U_i)` を出すための
  auxiliary RV 構成。
- **推奨**: `Common2026/Shannon/WynerZivConverseAux.lean` (新規) で
  `WynerZivAuxRV : Ω → U_i := fun ω => (W ω, Y^{i-1}_<i ω, Y^n_{>i} ω)` を定義し、Markov chain
  `U_i − X_i − Y_i` (i.i.d. source 仮定下) を補題化。
- **工数感**: ~100-150 行 (auxiliary RV definition + Markov chain 証明 + n-letter sum identity
  への lift)。
- **落とし穴**:
  - Markov chain `U_i − X_i − Y_i` は i.i.d. + Markov W-X-Y を要する。Y^n の隣接 `Y^{i-1}` /
    `Y^n_{>i}` は `X_i` 経由でしか `Y_i` に依存しない構造を Lean で正確に書く。
  - `(W, Y^{<i}, Y^{>i})` の型は `M × (Fin i → β) × (Fin (n-i-1) → β)`、これに対する `Fintype`
    + `MeasurableSingletonClass` instance は自動 derive されるが、**SBS は `Countable` 経由で
    `DiscreteMeasurableSpace` を有効化** する必要あり (§9)。

### P2 (Phase C converse の hypothesis pass-through)

#### (e) Csiszár's sum identity (`∑ I(X_i;U_i) - I(Y_i;U_i) = I(X^n;W) - I(Y^n;W) - (Markov terms)`)

- **目的**: n-letter chain rule のキーステップ。Cover-Thomas 15.9.2 の最重要補題。
- **推奨**: **L-WZ2 で hypothesis pass-through** (主定理に `h_csiszar` 引数として注入)。実装と
  しては既存 `mutualInfo_chain_rule_fin` + `condMutualInfo_eq_condEntropy_sub_condEntropy` の
  iteration で導出可能だが ~300 行の plumbing 工数 (別 plan で discharge)。
- **工数感** (本 plan): hypothesis 受け取りのみ ~10 行 / (別 discharge): ~300-400 行。
- **落とし穴**: identity の正確な statement は `∑ [I(X_i;W,Y^{<i}) - I(Y_i;W,Y^{<i})]
  = I(X^n;W) - I(Y^n;W)` で、index reshape 系の plumbing で爆発しやすい。

#### (f) n-letter Jensen for `R_WZ` (convexity in `D`)

- **目的**: Phase C で `R_WZ((1/n)∑D_i) ≤ (1/n) ∑ R_WZ(D_i)`。
- **推奨**: **L-WZ3 で hypothesis pass-through** (既存 RD converse n-letter で同戦略)。
- **工数感** (本 plan): hypothesis 受け取りのみ ~5 行 / (別 discharge): ~150 行。
- **落とし穴**: 凸性が成り立つことの証明には `wynerZivRatePmf` の domain `U` 拡張 (~U_1 ⊔ U_2) が
  要り、新規 ~100 行の補題が必要。

### P3 (補助)

#### (g) `wynerZivRate` の MeasurableEquiv 不変性 (auxiliary `U` reshape)

- **目的**: `U` の具体表現に依らない値であることを示す。
- **推奨**: `mutualInfo_map_left_measurableEquiv` (Common2026) と同型の証明 (~80 行)。
- **工数感**: ~80-100 行。
- **落とし穴**: `sInf` が `MeasurableEquiv` 不変なので bijective relabel 系は trivial だが、
  `|U|` の cardinality bound 系は L-WZ1 で別途扱う。

#### (h) Standard Borel instance for finite `U`

- **目的**: `condMutualInfo` 等の `[StandardBorelSpace U]` を充足するため。
- **推奨**: `instance : DiscreteMeasurableSpace U := ⟨fun _ _ => trivial⟩` (`U` が
  `MeasurableSingletonClass + Fintype` のとき)。これで `Countable + DiscreteMeasurableSpace ⇒
  StandardBorelSpace` の Mathlib 既存 instance 経由で derive 可能。
- **工数感**: ~10-20 行 (instance 群)。
- **落とし穴**: 既存 SlepianWolf / RateDistortion 系では `[Fintype + MSC]` を持つが SBS は仮定
  していない (`condMutualInfo` を回避している)。Wyner-Ziv では condMI 必須なので **新規に
  instance を立てる必要あり**。詳細は §9。

## 5. 撤退ラインへの距離

親計画の seed (Tier 3 T3-D, ~1000-1500 行) に対し、本在庫から導出される撤退ライン候補：

### L-WZ1: auxiliary cardinality bound `|U| ≤ |X| + 1` (Carathéodory 型 reduction)

- **理由**: Cover-Thomas 15.9 の補題 (`|U|` を有限に押さえる Carathéodory 系) は Lean 化が
  煩雑 (convex set の extreme point 構造を要する)。本 seed では **`U` を Fintype として
  受け取り** statement を `∀ (U : Type*) [Fintype U], ...` 形に保持。`|U|` 最小化は別 plan。
- **影響**: 主定理の rate function 値は変わらないが、**`R_WZ(D)` の compute 可能性** (実際の
  最適 `U` を構成するアルゴリズム) は別 plan で discharge。
- **工数削減**: ~200-300 行。

### L-WZ2: converse を auxiliary 形のまま publish (single-letterization を別 plan)

- **理由**: Csiszár's sum identity の n-letter chain rule discharge は ~300-400 行で本 seed
  scope を圧迫。**hypothesis `h_csiszar` を pass-through** して publish、別 plan で discharge。
- **影響**: `wynerZiv_converse_n_letter` の statement は `(h_csiszar : Csiszar_sum_identity ...) →
  ...` 形になるが、**主定理 R_WZ(D) ≤ R は到達**。
- **工数削減**: ~300-400 行 (別 plan で discharge 時に書く)。

### L-WZ3: 凸性 hypothesis pass-through

- **理由**: `wynerZivRatePmf` の `D` 凸性は auxiliary `U` domain 拡張経由で、Lean 化に ~100-150
  行。既存 `RateDistortionConverseNLetter.lean` の `h_jensen_antitone` パターンを踏襲し
  hypothesis pass-through。
- **影響**: Phase C で `h_jensen : R_WZ((1/n)∑D_i).toReal ≤ (1/n)∑ R_WZ(D_i).toReal` を仮定。
- **工数削減**: ~150 行 (別 plan で discharge)。

### 撤退ライン発動の総合判定

- 本 inventory の段階では **L-WZ1 / L-WZ2 / L-WZ3 全て発動を推奨**。発動後の主定理は SW
  achievability + RD converse n-letter と同じ hypothesis pass-through スタイル (本プロジェクトで
  既に確立済み、proof-log 平均 70-80% の plumbing 再利用率)。
- 発動しない場合 (3 件全て discharge) は **+650-850 行追加** (合計 ~1650-2350 行)、本 seed
  の seed 規模見積もり (1000-1500 行) を超過。

## 6. 危険箇所

最も事故りやすい 5 件 (優先順位順)：

### 6.1 `[StandardBorelSpace U]` instance の確保

`condMutualInfo` (定義 + 全 chain rule) は `[StandardBorelSpace X]` + `[StandardBorelSpace Y]`
を要求する。Wyner-Ziv では `U` を含む 3 種 (X, Y, U) で condMI が出るが、**Fintype +
MeasurableSingletonClass からは SBS が自動で出ない** — Mathlib 既存 instance は
`[Countable α][DiscreteMeasurableSpace α]` 経由 (`Polish/Basic.lean:119`)。

**回避策**: Phase A skeleton で
```lean
instance (priority := 100) {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] : DiscreteMeasurableSpace α := ⟨fun _ _ => trivial⟩
```
を locally 立てる (既存ファイル汚染を避けるため `Common2026/Shannon/WynerZivStandardBorel.lean`
独立 file)。**ただし global instance だと既存 Slepian-Wolf / Rate-Distortion ファイルの
typeclass 推論を変えてしまう恐れあり** — 必ず scoped or local。

### 6.2 Markov chain `U-X-Y` の Lean 化 (γ-form vs β-form)

既存 `IsMarkovChain` は **γ-form** (`Common2026/Shannon/CondMutualInfo.lean:71`):
```lean
def IsMarkovChain (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) : Prop :=
  μ.map (fun ω => (Zc ω, Xs ω, Yo ω))
    = (μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ))
```

Wyner-Ziv の Markov chain は **`U → X → Y`** で、上記の引数順 (`Xs → Zc → Yo`) と **逆方向**。
**argument order**: `Common2026` の `IsMarkovChain μ Xs Zc Yo` は「`Zc` を介して `Xs` と `Yo` が
条件付き独立」を意味するので、Wyner-Ziv の `U − X − Y` は `IsMarkovChain μ Us Xs Ys` で書ける
(条件付け side が `Xs`、両端が `Us, Ys`)。**読み違えると主定理の statement が反転する**。

### 6.3 三項 typicality `T^n_ε(X, Y, U)` の Lean 化

既存 `jointlyTypicalSet` (`Common2026/Shannon/ChannelCoding.lean:301`) は **二項
`α × β`**。Wyner-Ziv では 3 種 `(X, Y, U)` 上の jointly typical が要る。

**回避策**: 既存 `jointlyTypicalSet μ Xs Ys n ε` を `((X, Y), U)` の nested 形で再利用 (`Z :=
α × β`, `U` を残す)。**ただし single-axis typical condition が 3 つに増える** (`X` 単独 +
`Y` 単独 + `(X,Y)` 結合 + `U` 単独 + `(X,U)` 結合 + `(Y,U)` 結合 + `(X,Y,U)` 結合 = 7 条件)、
Cover-Thomas 15.9 では実は AEP の **二項合同型条件 (X, U joint typical) + (Y, U joint typical)**
だけ要るので、新規に `wynerZivJointlyTypicalSet` を定義し直す方が plumbing が軽い (~100 行)。

### 6.4 `R_WZ(D)` の凸性 (Mathlib 直接対応なし)

`I(X;U) - I(Y;U)` は **`U` の domain ではなく Markov constraint + distortion constraint 全体の
領域で凸性が言える** (Cover-Thomas 15.9 Theorem)。`stdSimplex` 上の凸性は **`I(X;U)` は
concave-in-q、`-I(Y;U)` は convex-in-q なので差は generic には neither**。Cover-Thomas は
domain 拡張 (`U' = U_1 ⊔ U_2` の disjoint union で `q'(x,y,u') = λ q_1(x,y,u_1) + (1-λ)
q_2(x,y,u_2)`) で凸化するが、**Lean では auxiliary alphabet を可変にする必要があり**、`Type*`
レベルでの reshape が必要。

**回避策**: L-WZ3 で hypothesis pass-through。本 inventory では「自作 ~150 行 (別 plan)」と
見積もる。

### 6.5 `RateDistortionAchievability.lean` の `RDConstraint` を直接拡張できない

既存 `RDConstraint P_X d D : Set (α × β → ℝ)` は **2 変数 pmf 上**。Wyner-Ziv では **3 変数
`α × β × U → ℝ`** が必要で、marginal constraint も "`(α, β)` marginal = `P_XY`" + Markov
constraint で増える。**既存 `RDConstraint` の単純な拡張ではなく、新規 `WZConstraint` を立てる**。

**落とし穴**: `expectedDistortionPmf` の引数も `α × β × U → ℝ` 上に持ち上げる必要があり、
`d : α → γ → ℝ` の `γ` (= 復号側 alphabet) は別の type であることに注意。実は Wyner-Ziv の
distortion は **`d(x, f(u, y))` の expectation** で、auxiliary `U` を直接 distortion arg に
取らない。decoder `f : U × β → γ` を **constraint set に組み込む** か **rate function
definition に外で受ける** かで Lean structure が大きく変わる。**推奨**: decoder を rate function
の外で `∃ f, ...` 形で受ける (sInf over `(q, f)` の組)。

## 7. 着手 skeleton (`Common2026/Shannon/WynerZiv.lean` 出だし)

> 30 行制限を遵守。Phase A 起点の最小骨格のみ。Phase B/C/D は別 file を分離想定 (sibling
> file `WynerZivAchievability.lean`, `WynerZivConverse.lean`)。

```lean
import Common2026.Shannon.RateDistortionAchievability
import Common2026.Shannon.RateDistortionConverseNLetter
import Common2026.Shannon.SlepianWolfBinning
import Common2026.Shannon.SlepianWolfConditionalTypicalSlice
import Common2026.Shannon.SlepianWolfFullRateRegion
import Common2026.Shannon.CondMutualInfo
import Common2026.Shannon.MIChainRule

/-!
# Wyner–Ziv lossy distributed coding (T3-D Phase A skeleton)

Cover-Thomas 15.9. Side-information `Y` (at decoder only) で source `X` を distortion
`D` 以下で再現する rate `R_WZ(D) = min_{p(u|x)} min_{f} [I(X;U) - I(Y;U)]`。

## Phase 構成 (本 file: Phase A のみ)

* Phase A: `wynerZivRatePmf` 定義 + 達成性 (`IsCompact.exists_isMinOn`)
* Phase B: achievability (random binning + jointly typical, ⇒ `WynerZivAchievability.lean`)
* Phase C: converse (n-letter chain rule + Csiszár's sum, ⇒ `WynerZivConverse.lean`)
* Phase D: 主定理 tendsto 形 (`WynerZiv.lean` 末尾で合流)

## 撤退ライン

* L-WZ1: auxiliary cardinality bound `|U| ≤ |X|+1` は別 plan
* L-WZ2: Csiszár's sum identity は hypothesis pass-through
* L-WZ3: `R_WZ(D)` 凸性は hypothesis pass-through
-/

namespace InformationTheory.Shannon.WynerZiv

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β γ : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
  [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]

/-! ## Phase A — Wyner-Ziv code structure + rate function -/

/-- Wyner-Ziv lossy code: encoder のみ X 側、decoder は (codeword, side info Y) → X̂. -/
structure WynerZivCode (M n : ℕ) (α β γ : Type*)
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] where
  encoder : (Fin n → α) → Fin M
  decoder : Fin M × (Fin n → β) → (Fin n → γ)

namespace WynerZivCode
variable {M n : ℕ}

/-- Expected block distortion under joint source `(P_X, P_Y)`. -/
noncomputable def expectedBlockDistortion
    (c : WynerZivCode M n α β γ) (P_XY : Measure (α × β))
    (d : DistortionFn α γ) : ℝ :=
  ∫ p : (Fin n → α) × (Fin n → β),
      blockDistortion d n p.1 (c.decoder (c.encoder p.1, p.2))
    ∂(Measure.pi (fun _ : Fin n => P_XY))

end WynerZivCode

/-- Wyner-Ziv rate function (pmf form). auxiliary alphabet `U` を引数で受ける
(`U` cardinality bound は L-WZ1 で defer). -/
noncomputable def wynerZivRatePmf
    (U : Type*) [Fintype U] [DecidableEq U] [Nonempty U]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) : ℝ := by sorry

/-- Achievability of `wynerZivRatePmf` minimizer (Phase A 達成性). -/
theorem wynerZivRatePmf_attained
    (U : Type*) [Fintype U] [DecidableEq U] [Nonempty U]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ)
    (h_ne : ∃ q : α × β × U → ℝ, ∃ f : U × β → γ,
              True /- placeholder constraint -/) :
    ∃ qStar : α × β × U → ℝ, ∃ fStar : U × β → γ,
      True /- wynerZivRatePmf U P_XY d D = ... qStar fStar -/ := by sorry

/-! ## Phase B — Achievability (forward declaration only; full proof in
`WynerZivAchievability.lean`) -/

theorem wynerZiv_achievability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (d : DistortionFn α γ) (D : ℝ) {R : ℝ}
    -- (auxiliary U + iid + Markov hypotheses elided in skeleton; concrete
    --  signature finalized in Phase B file)
    : True := by sorry

/-! ## Phase C — Converse (hypothesis pass-through form;
forward declaration only) -/

theorem wynerZiv_converse_single_shot
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → α) (Ys : Ω → β)
    (d : α → γ → ℝ)
    -- L-WZ2 + L-WZ3 hypothesis pass-through TBD
    : True := by sorry

/-! ## Phase D — main theorem `wynerZiv_tendsto` (合流; TBD) -/

end InformationTheory.Shannon.WynerZiv
```

(行数: 95 行 — 主定理 4 本 + 補助 structure 1 本 + namespace + import の skeleton。実装本体は
~1000-1500 行で別 file)

## 工数感 (Phase 0 後の見立て)

| Phase | 当初 seed 見積 | Phase 0 後の見立て | 差分 |
|---|---|---|---|
| Phase 0 (M0 — 本ファイル) | — | 完了 (1 ターン) | — |
| Phase A (rate function + achievement + 連続性) | ~250 行 | **~280-350 行** | L-WZ3 凸性 defer により ~30 行軽量化、ただし auxiliary `U` plumbing で ~80 行重量化 |
| Phase B (achievability binning + jointly typical) | ~500-800 行 | **~500-700 行** | 既存 SW binning + jointly typical decoder 流用で計画通り (overlap ~60%) |
| Phase C (converse with hypothesis pass-through) | ~250-450 行 | **~300-450 行** | L-WZ2 + L-WZ3 で本体は ~250 行 + auxiliary RV `U_i := (W, Y^{i-1}, Y^{>i})` 構成 ~100-150 行 |
| Phase D (合流 + tendsto) | — | **~50-80 行** | ChannelCoding / RD 既存パターン流用 |
| **累計** | ~1000-1500 行 | **~1130-1580 行** | 撤退ライン 3 本発動下で計画範囲内 |

撤退ライン 3 本を全 discharge する場合は **+650-850 行** で総計 ~1780-2430 行 (シード上限超過、
別 plan 推奨)。

## 既存 Slepian-Wolf + RateDistortion との overlap 度合

| 領域 | 流用率 |
|---|---|
| Random binning + jointly typical decoder (`SlepianWolfBinning.lean` + `SlepianWolfFullRateRegion.lean` ~2700 行) | **~60%** (`U^n` 上の binning に置換 + 2-way error decomposition 縮退で再利用) |
| `conditionalTypicalSlice` (`SlepianWolfConditionalTypicalSlice.lean` ~315 行) | **~80%** (slice X→Y を X→(U, Y) に拡張) |
| Rate-distortion achievability infrastructure (`RateDistortionAchievability.lean` ~660 行) | **~30%** (`LossyCode` structure / `expectedBlockDistortion` / `mutualInfoPmf` を WZ 用に拡張) |
| Rate-distortion converse n-letter (`RateDistortionConverseNLetter.lean` ~393 行) | **~70%** (single-letterization pattern + per-letter feasibility + hypothesis pass-through 完全踏襲) |
| Single-shot RD converse (`RateDistortionConverse.lean` ~213 行) | **~50%** (4-step chain entropy → MI → DPI → R(D̃) は構造同型、auxiliary U で 2 段増) |
| CondMI / MI chain rule (`CondMutualInfo.lean` + `MIChainRule.lean` ~1160 行) | **~95%** (そのまま流用、新規補題は instance 群と Csiszár's sum hypothesis のみ) |
| **全体** | **~65%** |

すなわち Wyner-Ziv は本プロジェクトの SW + RD インフラ完成後の **副系として 1/3 が新規** 規模。
撤退ライン 3 本発動下では **実質 ~600-900 行の新規 proof onset** に縮退。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-19 起草**: T3-D seed (textbook-roadmap.md Tier 3) からの Phase 0 在庫調査。
   loogle index + `rg` で MI / condMI / Markov chain / Slepian-Wolf binning / RateDistortion
   pmf 形 / Kernel API を確認。撤退ライン 3 本 (L-WZ1 cardinality bound / L-WZ2 Csiszár's sum
   / L-WZ3 凸性) を提案。auxiliary alphabet `U` の SBS instance を最大の危険箇所として記録。
