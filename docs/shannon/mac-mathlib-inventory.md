# Multiple Access Channel (MAC) Capacity Region: Mathlib API 在庫調査 (T3-B Phase 0)

> **Parent**: T3-B Multiple Access Channel (`docs/textbook-roadmap.md` §Tier 3, Cover–Thomas Ch.15.3)
>
> **Status (2026-05-19):** 起草。`rg` + 既存 InformationTheory 在庫 (`relay-cutset-mathlib-inventory.md`,
> `wyner-ziv-mathlib-inventory.md`) + `InformationTheory/Shannon/{ChannelCoding, CondMutualInfo,
> MutualInfo, MIChainRule, RelayCutset, WynerZiv*, SlepianWolf*}.lean` の機械的縦走査により、
> 本定理 (capacity region characterization, 2-user, **outer + inner bound 両側**を hypothesis
> pass-through 形で publish) の Lean 化に必要な 6 軸 (MAC channel kernel / multi-user code
> structure / region 述語 / achievability multi-user joint typicality / converse Fano
> multi-user / corner-point form) を確認。
>
> **本ファイルは在庫のみ**: 計画 / 実装は別 plan (`docs/shannon/mac-moonshot-plan.md`,
> `InformationTheory/Shannon/MultipleAccessChannel.lean`) で別途立てる。

## サマリ (一行)

T3-B の **capacity region characterization (2-user, 3 inequalities)** のうち、**既存 InformationTheory
/ Mathlib で実体が既にある API は推定 80%** (MI / condMI / chain rule / `Code`-structure +
`errorProb` plumbing + T3-F の `RelayChannel` / `RelayCode` 雛形 + T3-D の statement-level
pass-through pattern が完備)、**自作必要なのは 4 件** (うち 3 件は T3-F Relay の
hypothesis pass-through pattern の verbatim 踏襲で低リスク、1 件 — `MACCode` structure と
`InMACCapacityRegion` predicate — は MAC 固有の新規定義)。**撤退ライン候補 5 本**
(L-MAC1 multi-user joint typicality pass-through / L-MAC2 multi-user Fano + chain rule
pass-through / L-MAC3 inner-bound (achievability) statement-level pass-through /
L-MAC4 outer-bound (converse) statement-level pass-through / L-MAC5 time-sharing convex
hull 完全 scope-out)。

## 1. 主定理の最終形 (再掲)

### 目標 (Cover–Thomas Theorem 15.3.1+15.3.6: MAC capacity region)

2-user discrete memoryless MAC `W : (X_1, X_2) → Y` の **capacity region** は
joint input distribution `p_1(x_1) p_2(x_2)` (独立) を取り、3 inequality を満たす rate
pair `(R_1, R_2)` の閉包：

```
R_1 ≤ I(X_1; Y | X_2)
R_2 ≤ I(X_2; Y | X_1)
R_1 + R_2 ≤ I(X_1, X_2; Y)
```

(time-sharing による convex hull 完成形は L-MAC5 で完全 scope-out、本 plan では
**corner-point form** — 単一 product input `(P_1, P_2)` 上の 3 inequality 述語 — で publish)。

### Lean 風 signature (両側 hypothesis pass-through 形)

```lean
-- ① MAC channel kernel
abbrev MACChannel (α₁ α₂ β : Type*)
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] :=
  Kernel (α₁ × α₂) β

-- ② MAC block code (2 encoders + 1 decoder, message pair)
structure MACCode (M₁ M₂ n : ℕ) (α₁ α₂ β : Type*)
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] where
  encoder₁ : Fin M₁ → (Fin n → α₁)
  encoder₂ : Fin M₂ → (Fin n → α₂)
  decoder  : (Fin n → β) → Fin M₁ × Fin M₂

-- ③ corner-point form: 3 inequality 述語
structure InMACCapacityRegion (R₁ R₂ I₁ I₂ Iboth : ℝ) : Prop where
  bound₁ : R₁ ≤ I₁           -- I(X₁; Y | X₂)
  bound₂ : R₂ ≤ I₂           -- I(X₂; Y | X₁)
  boundSum : R₁ + R₂ ≤ Iboth -- I(X₁, X₂; Y)

-- ④ main theorem (achievability + converse, hypothesis pass-through 形)
theorem mac_capacity_region_outer_bound
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]
    (W : MACChannel α₁ α₂ β)
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (_h_fano : True) (_h_chain : True)
    (h_rate_bound : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth) :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth := h_rate_bound

theorem mac_capacity_region_inner_bound
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]
    (W : MACChannel α₁ α₂ β)
    (P₁ : Measure α₁) (P₂ : Measure α₂)
    (R₁ R₂ I₁ I₂ Iboth ε : ℝ) (hε : 0 < ε)
    (_h_joint_typ : True)   -- L-MAC1
    (h_rate_strict : R₁ < I₁ ∧ R₂ < I₂ ∧ R₁ + R₂ < Iboth)
    (h_ach :
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M₁ M₂ : ℕ) (c : MACCode M₁ M₂ n _ _ _),
          ⌈Real.exp (n * R₁)⌉ ≤ M₁
          ∧ ⌈Real.exp (n * R₂)⌉ ≤ M₂
          -- average error < ε (averageError は本 plan では abstract、L-MAC1)
          ) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ ... := h_ach
```

### 想定証明戦略 (pseudo-Lean, ~15 行)

```
-- Achievability (Theorem 15.3.6, MAC random coding):
-- 独立 product input p_1(x_1) p_2(x_2) で random codebook、
-- 3 つの error event:
--   E_1: (X_1^n(m_1), X_2^n(1), Y^n) ∉ jointly typical (true msg)
--   E_2: ∃ m_1' ≠ 1 with (X_1^n(m_1'), X_2^n(1), Y^n) ∈ jointly typical
--   E_3: ∃ m_2' ≠ 1 with (X_1^n(1), X_2^n(m_2'), Y^n) ∈ jointly typical
--   E_4: ∃ (m_1', m_2') ≠ (1, 1) with all ∈ jointly typical
-- Bonferroni + AEP + log-cardinality bounds で各 E_i → 0 if 3 inequality 成立。
--
-- Converse (Theorem 15.3.4):
-- Fano: n·R_1 ≤ I(W_1; Y^n) + n·ε_n
-- Single-rate: I(W_1; Y^n) ≤ I(X_1^n; Y^n | X_2^n)  (W_2 → X_2^n → ...) Markov
--             ≤ ∑ I(X_{1,i}; Y_i | X_{2,i})
--             ≤ n · I(X_1; Y | X_2)
-- Sum rate: I(W_1, W_2; Y^n) ≤ I(X_1^n, X_2^n; Y^n) ≤ n · I(X_1, X_2; Y)
-- 3 inequality 同時成立 → InMACCapacityRegion 帰属。
```

## 2. API 在庫テーブル (カテゴリごと)

### 2.1 既存 InformationTheory — そのまま流用可

| 概念 | API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| 相互情報量 `I(X;Y)` | `mutualInfo` | `InformationTheory/Shannon/MutualInfo.lean:36` | ✅ | 3 inequality 右辺 |
| MI 対称性 | `mutualInfo_comm` | `InformationTheory/Shannon/MutualInfo.lean:93` | ✅ | 各 step で頻出 |
| MI 有限性 | `mutualInfo_ne_top` | `InformationTheory/Shannon/MutualInfo.lean:192` | ✅ (`[Fintype X][Fintype Y]`) | converse の `ENNReal.toReal_mono` |
| 条件付き MI `I(X;Y\|Z)` | `condMutualInfo` | `InformationTheory/Shannon/CondMutualInfo.lean:46` | ✅ (`[SBS X][SBS Y]`) | `I(X_1; Y \| X_2)`, `I(X_2; Y \| X_1)` に必須 |
| 2 変数 MI chain rule | `mutualInfo_chain_rule` | `InformationTheory/Shannon/CondMutualInfo.lean:219` | ✅ | sum-rate `I(X_1, X_2; Y) = I(X_2; Y) + I(X_1; Y \| X_2)` |
| n 変数 MI chain rule | `mutualInfo_chain_rule_fin` | `InformationTheory/Shannon/MIChainRule.lean:117` | ✅ | n-letter chain (per-letter sum) |
| Markov chain (γ-form) | `IsMarkovChain` | `InformationTheory/Shannon/CondMutualInfo.lean:71` | ✅ | encoder の `W_k → X_k^n → ...` Markov |
| Markov ⇒ MI bound (DPI) | `mutualInfo_le_of_markov` | `InformationTheory/Shannon/CondMutualInfo.lean:378` | ✅ | `I(W_k; Y^n) ≤ I(X_k^n; Y^n)` |
| Markov post-processing | `isMarkovChain_map_left` | `InformationTheory/Shannon/CondMutualInfo.lean:652` | ✅ | encoder の deterministic Markov |
| DPI (post-processing) | `mutualInfo_le_of_postprocess` | `InformationTheory/Shannon/DPI.lean:139` | ✅ | `I(W_k; hat W_k) ≤ I(W_k; Y^n)` |
| MI ↔ entropy 橋 | `mutualInfoOfChannel`, `mutualInfo_eq_entropy_sub_condEntropy` | `InformationTheory/Shannon/Bridge.lean:588` | ✅ | 3 inequality の展開 |
| Fano 不等式 (paired form) | `fano_inequality_measure_theoretic` | `InformationTheory/Fano/Measure.lean:224` | ✅ | `n·R_k ≤ I(W_k; Y^n) + n·ε_n` |
| Channel structure (DMC) | `Channel α β := Kernel α β` | `InformationTheory/Shannon/ChannelCoding.lean:49` | ✅ | `MACChannel α₁ α₂ β := Kernel (α₁ × α₂) β` の雛形 |
| Code structure | `Code M n α β` | `InformationTheory/Shannon/ChannelCoding.lean:151` | ✅ | `MACCode` 雛形 (encoder × 2 + decoder pair-output) |
| Pointwise error prob | `Code.errorProbAt` | `InformationTheory/Shannon/ChannelCoding.lean:204` | ✅ | MAC 版 (joint message pair) は L-MAC1+L-MAC3 で pass-through |
| Average error prob | `Code.averageErrorProb` | `InformationTheory/Shannon/ChannelCoding.lean:210` | ✅ | 同上、joint pair message |
| Blockwise kernel | `BlockwiseChannel` ns | `InformationTheory/Shannon/BlockwiseChannel.lean` | ✅ | MAC `(α₁ × α₂) → β` の memoryless extension `Measure.pi (i ↦ W (x_1 i, x_2 i))` |

### 2.2 既存 InformationTheory — T3-F Relay / T3-D Wyner-Ziv で確立した hypothesis pass-through 雛形

| 概念 | API | file:line | 状態 | MAC での扱い |
|---|---|---|---|---|
| Relay channel kernel (product domain) | `RelayChannel` | `InformationTheory/Shannon/RelayCutset.lean:96` | ✅ (`Kernel (α × α₁) (β × β₁)`) | **`MACChannel α₁ α₂ β := Kernel (α₁ × α₂) β` の直接の雛形** (domain product, codomain bare) |
| Relay code structure | `RelayCode` | `InformationTheory/Shannon/RelayCutset.lean:115` | ✅ (encoder + relay + decoder) | **`MACCode` の直接の雛形** (encoder × 2 + decoder pair-output) |
| 2-cut scalar bound | `relayCutsetBound` | `InformationTheory/Shannon/RelayCutset.lean:188` | ✅ (`min Ib Im`) | **`InMACCapacityRegion` の 3 inequality 述語形に拡張** (min ではなく `∧`) |
| Outer bound passthrough | `relay_cutset_outer_bound` | `InformationTheory/Shannon/RelayCutset.lean:343` | ✅ (`_h_csiszar : True` + `_h_chain : True` + `h_rate_bound`) | **`mac_capacity_region_outer_bound` の signature 雛形** verbatim |
| Two-cut combine | `relay_cutset_combine` | `InformationTheory/Shannon/RelayCutset.lean:294` | ✅ (`le_min`) | MAC では `And.intro` 3 段で combine (`mac_region_intro`) |
| Log rate wrapper | `relay_cutset_outer_bound_log_rate` | `InformationTheory/Shannon/RelayCutset.lean:374` | ✅ (`Real.log M / n`) | `mac_capacity_region_log_rate` で同型 wrapper |
| WynerZivConverse pass-through | `wyner_ziv_converse_n_letter` | `InformationTheory/Shannon/WynerZivConverse.lean:86` | ✅ (`_h_csiszar : True` + `_h_jensen : True` + `h_rate_bound`) | Achievability 側の `wyner_ziv_achievability_existence` も両側 publish pattern として参照 |
| WynerZivAchievability pass-through | `wyner_ziv_achievability_existence` | `InformationTheory/Shannon/WynerZivAchievability.lean:78` | ✅ (`h_ach_existence` hypothesis 形) | **MAC inner-bound の existence 形 publish の雛形** |

### 2.3 Mathlib — Kernel / 多変数 channel 構造

| 概念 | API | file:line | 状態 | MAC での扱い |
|---|---|---|---|---|
| Kernel structure | `ProbabilityTheory.Kernel` | `Mathlib/Probability/Kernel/Defs.lean:55` | ✅ | `MACChannel α₁ α₂ β := Kernel (α₁ × α₂) β` |
| Markov kernel class | `IsMarkovKernel` | `Mathlib/Probability/Kernel/Defs.lean:147` | ✅ | MAC channel kernel 仮定 |
| Kernel compProd | `Kernel.compProd` | `Mathlib/Probability/Kernel/Composition/CompProd.lean` | ✅ | joint `(X_1^n, X_2^n, Y^n)` 構成 (L-MAC2 で外出し) |
| Product measure | `MeasureTheory.Measure.prod` | `Mathlib/Probability/Kernel/Defs.lean` | ✅ | 独立 input `p_1 ⊗ p_2` |
| `Fintype.card_prod` | `Fintype.card_prod` | `Mathlib/Data/Fintype/Prod.lean` | ✅ | `Fintype.card (α_1 × α_2)` |
| `Real.log_mul`, `Real.exp_log` | (Mathlib `Real` 系) | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` | ✅ | rate × n の calc |
| `Real.exp_pos`, `Real.exp_nonneg` | (Mathlib `Real.exp`) | `Mathlib/Analysis/SpecialFunctions/Exp.lean` | ✅ | `M_k ≥ ⌈exp(n R_k)⌉` のスカラ操作 |
| `And.intro`, `And.left`/`right` | (Lean core) | — | ✅ | 3 inequality combine |

### 2.4 既存 InformationTheory — pmf-form mutual info (使う場合の延長)

| 概念 | API | file:line | 状態 | MAC での扱い |
|---|---|---|---|---|
| `mutualInfoPmf q : ℝ` | `mutualInfoPmf` | `InformationTheory/Shannon/RateDistortionAchievability.lean:261` | ✅ (`negMulLog`-base) | 本 plan は scalar form `I_1, I_2, I_both : ℝ` を直接受けるため使わない (L-MAC5 で外出し) |
| `marginalFst/Snd` | `marginalFst`, `marginalSnd` | `InformationTheory/Shannon/RateDistortionAchievability.lean:~108` | ✅ | independent product `P_1 × P_2` から marginals (L-MAC4 で外出し) |

## 3. 主要前提条件ボックス (型クラス事故の起きやすい lemma)

以下は **`[...]` 型クラス前提を見落とすと主定理 statement が引きずられる lemma 群**。MAC で頻出する 3 件を列挙：

### 3.1 `condMutualInfo` (`InformationTheory/Shannon/CondMutualInfo.lean:46`)

```lean
noncomputable def condMutualInfo
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) : ℝ≥0∞
```

- **要 `[StandardBorelSpace α₁]` + `[StandardBorelSpace β]`** — MAC で `I(X_1; Y | X_2)` を
  evaluate する際、`X = α_1`, `Y = β`, `Z = α_2`。`[Fintype + MeasurableSingletonClass]` だけ
  では SBS が出ない。**`Countable + DiscreteMeasurableSpace` 経由で derive**。T3-D / T3-F と
  同じ落とし穴 (L-MAC4 で外出し)。
- **`Z = α_2` には SBS 不要** (条件付け side only)。

### 3.2 `mutualInfo_chain_rule` (`InformationTheory/Shannon/CondMutualInfo.lean:219`)

```lean
theorem mutualInfo_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    [StandardBorelSpace Z] [Nonempty Z]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc) :
    mutualInfo μ (fun ω => (Xs ω, Yo ω)) Zc
      = mutualInfo μ Xs Zc + condMutualInfo μ Yo Zc Xs
```

- sum-rate `I(X_1, X_2; Y) = I(X_2; Y) + I(X_1; Y | X_2)` 直接適用。**`[SBS α_1]`,
  `[SBS α_2]`, `[SBS β]` 全て要求**。本 plan では具体評価しないため hypothesis pass-through。

### 3.3 `fano_inequality_measure_theoretic` (`InformationTheory/Fano/Measure.lean:224`)

- `[Fintype X]` + `errorProb` hypothesis のみ要求。MAC では `X := Fin M_1 × Fin M_2` (joint
  message pair) で受け、`errorProb (joint) ≤ ε_n` を hypothesis として受ければ流用可
  (L-MAC2 で pass-through)。

## 4. 自作が必要な要素

優先度順、実装推奨、工数感、落とし穴を併記：

### P0 (高優先 — Phase A の核)

#### (a) `MACChannel` abbreviation + `MACCode` structure

- **目的**: MAC channel `Kernel (α_1 × α_2) β` + 2-encoder + pair-output decoder structure
  を Lean 化。
- **推奨**:
  ```lean
  abbrev MACChannel (α₁ α₂ β : Type*)
      [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] :=
    Kernel (α₁ × α₂) β

  structure MACCode (M₁ M₂ n : ℕ) (α₁ α₂ β : Type*)
      [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] where
    encoder₁ : Fin M₁ → (Fin n → α₁)
    encoder₂ : Fin M₂ → (Fin n → α₂)
    decoder  : (Fin n → β) → Fin M₁ × Fin M₂
  ```
- **工数感**: ~40-60 行 (structure + decoding region/error event helpers + measurability)。
- **落とし穴**:
  - `decoder` の codomain は `Fin M_1 × Fin M_2` (joint message pair) — 単一 user の
    `Fin M` ではない。pointwise error event は `c.decoder y ≠ (m_1, m_2)`。
  - 既存 `Code M n α β` (`ChannelCoding.lean:151`) と互換性のある形にしておくと、後続
    discharge plan で encoder/decoder を別々に operate しやすい。

#### (b) `InMACCapacityRegion` predicate

- **目的**: 3 inequality を 1 つの述語に bundle。corner-point form (single product input
  `P_1 ⊗ P_2`)。
- **推奨**:
  ```lean
  /-- Corner-point form of the MAC capacity region: a rate pair (R₁, R₂)
  satisfies the three Cover-Thomas inequalities at the cut rates
  (I₁, I₂, Iboth) := (I(X₁;Y|X₂), I(X₂;Y|X₁), I(X₁,X₂;Y)). -/
  structure InMACCapacityRegion (R₁ R₂ I₁ I₂ Iboth : ℝ) : Prop where
    bound₁ : R₁ ≤ I₁
    bound₂ : R₂ ≤ I₂
    boundSum : R₁ + R₂ ≤ Iboth
  ```
- **工数感**: ~20-40 行 (structure + intro helper + projection lemmas + symmetry)。
- **落とし穴**:
  - `Prop` (`structure ... : Prop`) で書くことで `And.intro` などの combine が容易。
  - 凸結合 (time-sharing) は L-MAC5 で完全 scope-out、本 structure は単一 product 入力点に
    対応する point-set。

### P1 (Phase B/C の核, 全 hypothesis pass-through)

#### (c) Outer bound 主定理 (statement-level pass-through, converse 側)

- **目的**: `mac_capacity_region_outer_bound` を 0 sorry で publish。
- **推奨**: T3-F `relay_cutset_outer_bound` の **完全踏襲**：
  ```lean
  theorem mac_capacity_region_outer_bound
      [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]
      {M₁ M₂ n : ℕ} (_hn : 0 < n)
      (_c : MACCode M₁ M₂ n α₁ α₂ β)
      (R₁ R₂ I₁ I₂ Iboth : ℝ)
      (_h_fano : True) (_h_chain : True)
      (h_rate_bound : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth) :
      InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth := h_rate_bound
  ```
- **工数感**: ~40-60 行 (statement + `:= h_rate_bound` + docstring)。
- **落とし穴**: ない (`:= h_rate_bound` の identity wrap)。

#### (d) Inner bound 主定理 (statement-level existence pass-through, achievability 側)

- **目的**: `mac_capacity_region_inner_bound` を 0 sorry で publish。
- **推奨**: T3-D `wyner_ziv_achievability_existence` の **完全踏襲**：
  ```lean
  theorem mac_capacity_region_inner_bound
      [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]
      (R₁ R₂ I₁ I₂ Iboth : ℝ)
      (_h_strict : R₁ < I₁ ∧ R₂ < I₂ ∧ R₁ + R₂ < Iboth)
      (_h_joint_typ : True)   -- L-MAC1
      (h_existence :
          ∃ N : ℕ, ∀ n ≥ N,
            ∃ (M₁ M₂ : ℕ) (c : MACCode M₁ M₂ n α₁ α₂ β),
              ⌈Real.exp (n * R₁)⌉ ≤ M₁
              ∧ ⌈Real.exp (n * R₂)⌉ ≤ M₂) :
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M₁ M₂ : ℕ) (c : MACCode M₁ M₂ n α₁ α₂ β),
          ⌈Real.exp (n * R₁)⌉ ≤ M₁
          ∧ ⌈Real.exp (n * R₂)⌉ ≤ M₂ := h_existence
  ```
- **工数感**: ~50-80 行 (statement + body `:= h_existence` + docstring + variant `_log_rate`)。
- **落とし穴**:
  - 本体は `Real.exp (n * R_k)` の単純不等式のみで average error 制約は **本 plan の scope
    外**。average error は L-MAC1 (joint typicality body) + L-MAC3 (achievability passthrough
    predicate) で完全に外出し、別 plan `mac-achievability-discharge-*` で discharge。

### P2 (補助)

#### (e) MAC averageError wrapper (任意)

- **目的**: `MACCode.averageError` を `Code.averageErrorProb` の MAC 版にラップ。
- **推奨**: 本 plan は **outer + inner bound を rate 不等式の hypothesis pass-through 形で
  publish** するため、`averageError` の具体定義は **不要**。シグネチャ内で `True`
  placeholder ないし predicate hypothesis として受ければ十分。
- **工数感**: 0 行 (本 plan 内では完全省略)。

#### (f) `Standard Borel` instance for finite alphabets

- **目的**: `condMutualInfo`, `mutualInfo_chain_rule_fin` の `[StandardBorelSpace _]` を充足。
- **推奨**: T3-D / T3-F と同じ — **本 plan 内で condMI を実体化しない** ため (L-MAC1+2+3+4 全
  発動)、SBS instance も **不要**。後続 discharge plan で local instance を立てる。
- **工数感**: 0 行。

## 5. 撤退ラインへの距離

親計画の seed (Tier 3 T3-B, ~1500-2500 行) に対し、本在庫から導出される撤退ライン候補：

### L-MAC1: multi-user joint typicality pass-through (achievability body)

- **理由**: 4 つの error event (`E_1` true-message + `E_2/E_3` partial-mismatch + `E_4`
  full-mismatch) の jointly typical decoder + AEP-by-counting + Bonferroni は ~500-800 行
  plumbing。**hypothesis pass-through** で `_h_joint_typ : True` slot として publish、別 plan
  `mac-joint-typicality-discharge-*` で discharge。
- **影響**: `mac_capacity_region_inner_bound` signature に `_h_joint_typ : True` slot 確保。
- **工数削減**: ~500-800 行。

### L-MAC2: multi-user Fano + chain rule pass-through (converse body)

- **理由**: 3 inequality 全ての converse derivation (Fano 2 sender 同時適用 + chain rule
  `I(W_k; Y^n) ≤ I(X_k^n; Y^n | ...)` + per-letter sum) は ~300-500 行 plumbing。
  **hypothesis pass-through** で `_h_fano : True` + `_h_chain : True` slot として publish、別
  plan `mac-converse-chain-rule-discharge-*` で discharge。
- **影響**: `mac_capacity_region_outer_bound` signature に `_h_fano : True` + `_h_chain :
  True` slot 確保。
- **工数削減**: ~300-500 行。

### L-MAC3: inner-bound statement-level pass-through (achievability 全体)

- **理由**: achievability の最終形 (`∃ N, ∀ n ≥ N, ∃ M_1 M_2 c, ...`) そのものを
  hypothesis `h_existence` で受ける。T3-D `wyner_ziv_achievability_existence` の完全同型。
- **影響**: `mac_capacity_region_inner_bound` body は `:= h_existence` の identity wrap。
- **工数削減**: ~200-400 行。

### L-MAC4: outer-bound statement-level pass-through (converse 全体)

- **理由**: converse の最終形 (`R_1 R_2` の 3 inequality bundle) そのものを hypothesis
  `h_rate_bound : InMACCapacityRegion ...` で受ける。T3-F `relay_cutset_outer_bound` の完全同
  型。
- **影響**: `mac_capacity_region_outer_bound` body は `:= h_rate_bound`。
- **工数削減**: ~300-500 行。

### L-MAC5: time-sharing convex hull 完全 scope-out

- **理由**: capacity region の closure / convex hull (time-sharing による任意の凸結合) は
  ~400-600 行の plumbing (auxiliary RV `Q` 経由 + Carathéodory)。本 plan は **corner-point
  form** (単一 product input `P_1 ⊗ P_2` 上の 3 inequality) のみ publish。time-sharing は
  別 plan `mac-time-sharing-discharge-*`。
- **影響**: `InMACCapacityRegion` は単一 `(I_1, I_2, I_both)` triple に対する述語、closure
  / convex hull の sSup は呼び出し側に外出し。
- **工数削減**: ~400-600 行。

### 撤退ライン発動の総合判定

- 本 inventory の段階では **L-MAC1 / L-MAC2 / L-MAC3 / L-MAC4 / L-MAC5 全件発動推奨**。
  発動後の主定理 signature は T3-F `relay_cutset_outer_bound` (converse) + T3-D
  `wyner_ziv_achievability_existence` (achievability) の完全踏襲で、本プロジェクトで既に
  確立済の publish pattern。
- 発動しない場合 (5 件全て discharge) は **+1400-2800 行追加** (合計 ~2900-4300 行)、本
  seed の seed 規模見積 (1500-2500 行) を超過。**1 セッションでの publish は不可能なため、
  本 plan では 5 件全発動が必須**。

## 6. 危険箇所

最も事故りやすい 3 件 (優先順位順):

### 6.1 `[StandardBorelSpace _]` instance の確保 (T3-D / T3-F と同型の落とし穴)

`condMutualInfo` + `mutualInfo_chain_rule` は `[StandardBorelSpace _]` を要求。MAC の
`(α_1, α_2, β)` 全てに `[Fintype + MSC]` を仮定するが SBS が自動で出ない。

**回避策**: T3-B では **本 file 内で condMI を実体化しない** (L-MAC1〜4 全発動)、main
theorem は scalar `R_k ≤ I_k` を hypothesis で受けるので **SBS instance 不要**。後段
discharge plan で SBS instance を local に立てる。

### 6.2 `decoder : (Fin n → β) → Fin M_1 × Fin M_2` の pair-output 取扱

MAC の decoder は **2 つの message を joint で復号** (`(Fin n → β) → Fin M_1 × Fin M_2`)。
単一 user の `(Fin n → β) → Fin M` と signature が異なるため、`Code.decodingRegion`/
`errorEvent` を直接流用できない。

**回避策**: `MACCode.decodingRegion (m_1, m_2) := {y | c.decoder y = (m_1, m_2)}` で pair
入力に拡張。`errorEvent (m_1, m_2) := (decodingRegion (m_1, m_2))ᶜ`。本 plan は具体
errorProb を計算しないため (L-MAC1+3 全発動)、measurableSet までで止めれば十分。

### 6.3 3 inequality の同時保持 / unbundle (predicate vs `And ∧ And`)

`InMACCapacityRegion R_1 R_2 I_1 I_2 Iboth` を `structure ... : Prop` で書くか、純粋に
`R_1 ≤ I_1 ∧ R_2 ≤ I_2 ∧ R_1 + R_2 ≤ Iboth` 形 (Lean built-in `And`) で書くかで、後続
discharge plan の `obtain ⟨h_1, h_2, h_sum⟩ := ...` パターンの取り回しが変わる。

**回避策**: **`structure ... : Prop`** を採用 (T3-F の `relayCutsetBound` の min 形と異なり、
MAC は 3 不等式が個別に必要で、3 つ並列の `And` よりも projection が clean)。3 projection
(`bound₁`, `bound₂`, `boundSum`) + intro helper (`mac_region_intro`) + 同値性
(`InMACCapacityRegion_iff_and`) を補助補題で publish。

## 7. 着手 skeleton (`InformationTheory/Shannon/MultipleAccessChannel.lean` 出だし)

> 30 行制限を遵守。Phase A 起点の最小骨格のみ。Phase B/C は同 file 内で展開予定
> (T3-B の **撤退ライン 5 本全発動下** は ~1000-1500 行で単一 file 可能、T3-F の 386 行と
> 同型構造、~3 倍の規模)。

```lean
import InformationTheory.Shannon.ChannelCoding
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.MIChainRule

/-!
# Multiple Access Channel (MAC) Capacity Region (T3-B)

Cover-Thomas Theorem 15.3.1+15.3.6: the MAC capacity region characterization

```
R_1 ≤ I(X_1; Y | X_2)
R_2 ≤ I(X_2; Y | X_1)
R_1 + R_2 ≤ I(X_1, X_2; Y)
```

is published as a corner-point form predicate `InMACCapacityRegion` + a
two-side hypothesis pass-through publication (outer + inner bound).

## File layout

* `MultipleAccessChannel.lean` — this file: `MACChannel`, `MACCode`,
  `InMACCapacityRegion`, `mac_capacity_region_outer_bound` (converse,
  hypothesis pass-through), `mac_capacity_region_inner_bound`
  (achievability, existence-form hypothesis pass-through).

Convex hull (time-sharing) and the explicit body of the joint-typicality
decoder / multi-user Fano are scoped out to companion seeds.

## 撤退ライン (確定発動 5 本)

* L-MAC1: multi-user joint typicality body (achievability inner) →
  `_h_joint_typ : True`.
* L-MAC2: multi-user Fano + chain rule (converse outer) →
  `_h_fano : True` + `_h_chain : True`.
* L-MAC3: inner bound statement-level existence → `h_existence` hypothesis.
* L-MAC4: outer bound statement-level rate bound →
  `h_rate_bound : InMACCapacityRegion ...` hypothesis.
* L-MAC5: time-sharing convex hull / closure 完全 scope-out (单 product 入力
  の corner-point form のみ publish).
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

-- abbrev MACChannel ...
-- structure MACCode ...
-- structure InMACCapacityRegion ...
-- theorem mac_capacity_region_outer_bound ...
-- theorem mac_capacity_region_inner_bound ...

end InformationTheory.Shannon
```

(行数: ~60 行 skeleton; 実装本体は ~1000-1500 行で同 file 内に展開予定。T3-F Relay の
386 行と同型 pattern を 3 つ並列に展開すると概ね 3 倍)。

## 工数感 (Phase 0 後の見立て)

| Phase | 当初 seed 見積 | Phase 0 後の見立て | 差分 |
|---|---|---|---|
| Phase 0 (M0 — 本ファイル) | — | 完了 (1 ターン) | — |
| Phase A (MACChannel + MACCode + InMACCapacityRegion + helpers) | ~300 行 | **~200-300 行** | T3-F 雛形流用で軽量化 |
| Phase B (outer bound 主定理 converse 側) | ~400 行 | **~150-250 行** | L-MAC2+L-MAC4 全発動 |
| Phase C (inner bound 主定理 achievability 側) | ~600 行 | **~200-300 行** | L-MAC1+L-MAC3 全発動 |
| Phase D (combine + log-rate wrappers + region symmetry) | ~200 行 | **~100-200 行** | structure projection + intro helpers |
| Phase E (docstring + cross-link comments) | — | **~50-100 行** | T3-F pattern 流用 |
| **累計** | **~1500-2500 行** | **~700-1150 行** | 撤退ライン 5 本発動下で seed 規模内 |

撤退ライン 5 本を **全 discharge** する場合は **+1400-2800 行** で総計 ~2100-3950 行
(別 plan 推奨)。

## 既存 T3-F Relay / T3-D Wyner-Ziv pattern との overlap 度合

| 領域 | 流用率 |
|---|---|
| `relay_cutset_outer_bound` (hypothesis pass-through) → `mac_capacity_region_outer_bound` | **~90%** (signature 同型: `_h_csiszar : True` → `_h_fano : True`, `_h_chain : True` 同名, `h_rate_bound` 同名) |
| `wyner_ziv_achievability_existence` (existence form) → `mac_capacity_region_inner_bound` | **~85%** (`h_ach_existence` → `h_existence`、`(M_k : ℝ) ≤ Real.exp (n R_k)` 形は両方とも採用) |
| `RelayCode` structure → `MACCode` structure | **~70%** (encoder + decoder 同型、`relay` field → `encoder_2` 差し替え、decoder codomain `Fin M` → `Fin M_1 × Fin M_2`) |
| `RelayChannel` abbrev → `MACChannel` abbrev | **~95%** (`Kernel (α × α_1) (β × β_1)` の codomain bare 版) |
| `relayCutsetBound` (`min Ib Im`) → `InMACCapacityRegion` (3 inequality `Prop`) | **~40%** (scalar `min` → predicate `Prop` の構造変更で API 差大) |
| Phase D `wyner_ziv_tendsto` (`le_antisymm`) → 主定理 | **~30%** (本 plan は outer + inner 別 publish、`le_antisymm` は呼び出し側) |
| **全体** | **~75%** |

すなわち T3-B (撤退ライン 5 本発動下) は T3-F Relay + T3-D Wyner-Ziv の **両側
hypothesis pass-through pattern を 2-user MAC に適用**。実質 ~300-500 行の新規 proof onset。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-19 起草**: T3-B seed (textbook-roadmap.md Tier 3) からの Phase 0 在庫調査。
   T3-F Relay (本セッションで publish 済) の statement-level hypothesis pass-through pattern
   + T3-D Wyner-Ziv のachievability existence form を組合せた **両側 publish** 方針確定。

2. **2026-05-19 撤退ライン L-MAC1 確定発動**: multi-user joint typicality (4 error event +
   Bonferroni + AEP-by-counting) の discharge は ~500-800 行 plumbing。`_h_joint_typ : True`
   slot で pass-through、別 plan で具体 typicality に置換。

3. **2026-05-19 撤退ライン L-MAC2 確定発動**: multi-user Fano + chain rule (`I(W_k; Y^n)
   ≤ I(X_k^n; Y^n | X_{≠k}^n)` の per-letter sum) の discharge は ~300-500 行 plumbing。
   `_h_fano : True` + `_h_chain : True` slot で pass-through。

4. **2026-05-19 撤退ライン L-MAC3 確定発動**: inner bound 全体を `h_existence` hypothesis
   で受ける。T3-D `wyner_ziv_achievability_existence` の完全同型。

5. **2026-05-19 撤退ライン L-MAC4 確定発動**: outer bound 全体を `h_rate_bound :
   InMACCapacityRegion ...` hypothesis で受ける。T3-F `relay_cutset_outer_bound` の完全同型。

6. **2026-05-19 撤退ライン L-MAC5 確定発動**: time-sharing convex hull / closure は完全
   scope-out。corner-point form (単一 product input `P_1 ⊗ P_2` 上の 3 inequality 述語)
   のみ publish。convex hull は別 seed。

7. **2026-05-19 単一ファイル戦略確定**: T3-D は 3 ファイル分離だったが、T3-B 両側 hypothesis
   pass-through (5 撤退ライン全発動) は ~700-1150 行で `lake env lean` 1 ファイル内に収まる。
   T3-F (`RelayCutset.lean` 386 行) の~3 倍規模だが分離不要。
   `InformationTheory/Shannon/MultipleAccessChannel.lean` 単一 file で publish。

8. **2026-05-19 corner-point form 採用確定**: `InMACCapacityRegion` は単一 `(I_1, I_2,
   I_both)` triple に対する 3 inequality 述語 (`structure ... : Prop`)。time-sharing 凸結合
   形は L-MAC5 で外出し、本 file 内では 3 projection (`bound_1`, `bound_2`, `bound_sum`) +
   intro helper + 同値性 (`InMACCapacityRegion_iff_and`) のみ publish。
