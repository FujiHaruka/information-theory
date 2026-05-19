# Relay Channel + Cut-set Outer Bound: Mathlib API 在庫調査 (T3-F Phase 0)

> **Parent**: T3-F Relay Channel + Cut-set bound (Cover-Thomas Ch.15.7 ;
> `docs/textbook-roadmap.md` §Tier 3)
>
> **Status (2026-05-19):** 起草。loogle index (`.lake/build/loogle.index`) + Mathlib /
> Common2026 直 `rg` で本定理 (outer bound only, inner bound は完全 scope-out) の Lean 化
> に必要な 6 軸 (cut-set rate 定義 / relay channel kernel / mutual info I(X,X₁;Y) /
> conditional MI I(X;Y,Y₁|X₁) / n-letter Fano + chain rule / max-min outer bound) を
> 機械的に確認。各候補補題は **CLAUDE.md「Subagent Inventory of Mathlib Lemmas」** に従って
> 位置 / 完全シグネチャ ([..] 型クラス verbatim) / 引数 / 結論形 を記録する。
>
> **本ファイルは在庫のみ**: 計画 / 実装は別 plan (`docs/shannon/relay-cutset-moonshot-plan.md`,
> `Common2026/Shannon/RelayCutset.lean`) で別途立てる。

## サマリ (一行)

T3-F outer bound のうち、**既存 Common2026 / Mathlib で実体が既にある API は推定 75%**
(MI / condMI / chain rule / `Code`-structure + `errorProb` plumbing が完備)、
**自作必要なのは 5 件** (うち 3 件は T3-D Wyner-Ziv の statement-level pass-through pattern
の完全踏襲で低リスク、2 件 — `RelayCode` structure + `relayCutsetBound` 定義 — は
relay channel 固有の新規定義)。**撤退ライン候補 4 本** (L-RC1 Csiszár's sum identity
pass-through / L-RC2 auxiliary chain rule pass-through / L-RC3 statement-level main
theorem pass-through / L-RC4 measurability bundle defer)。inner bound は完全 scope-out
(decode-and-forward / compress-and-forward は別 seed)。

## 1. 主定理の最終形 (再掲)

### 目標 (Cover-Thomas Theorem 15.10.1: cut-set outer bound)

relay channel `(X, X_1) → (Y, Y_1)` (sender X, relay (X_1 input, Y_1 output),
receiver Y) の **cut-set outer bound**:

```
C ≤ max_{p(x, x_1)} min { I(X, X_1; Y),  I(X; Y, Y_1 | X_1) }
```

すなわち、任意の達成可能 rate `R` (= capacity `C` の上限値) は、joint input
distribution `p(x, x_1)` 上で `(I(X, X_1; Y), I(X; Y, Y_1 | X_1))` の最小値の
最大値以下。

### Lean 風 signature (outer bound only, hypothesis pass-through 形)

```lean
-- ① relay channel structure (Kernel signature)
abbrev RelayChannel (α α₁ β β₁ : Type*)
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁] :=
  Kernel (α × α₁) (β × β₁)

-- ② relay code (sender encoder + per-step relay function + receiver decoder)
structure RelayCode (M n : ℕ) (α α₁ β β₁ : Type*)
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁] where
  encoder : Fin M → (Fin n → α)
  -- relay reads past Y₁ outputs, produces next X₁ input.
  -- For the outer bound publish we keep the relay as a deterministic causal
  -- function from past Y₁ to current X₁.
  relay : ∀ (i : Fin n), (Fin i.val → β₁) → α₁
  decoder : (Fin n → β) → Fin M

-- ③ cut-set rate function (max-min over joint pmf p(x, x_1))
noncomputable def relayCutsetBound
    (P : α × α₁ → ℝ)
    (I_broadcast : α × α₁ → ℝ)   -- I(X, X_1; Y) at joint pmf P
    (I_mac       : α × α₁ → ℝ) : -- I(X; Y, Y_1 | X_1) at joint pmf P
    ℝ :=
  min (I_broadcast P) (I_mac P)

-- ④ main theorem (outer bound, hypothesis pass-through 形, n-letter Fano + chain rule)
theorem relay_cutset_outer_bound
    [Fintype α] [Fintype α₁] [Fintype β] [Fintype β₁]
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (W : RelayChannel α α₁ β β₁)
    {M n : ℕ} (hn : 0 < n)
    (c : RelayCode M n α α₁ β β₁)
    (R : ℝ)
    -- L-RC3: composite cut-set rate bound supplied as hypothesis.
    (h_rate_bound :
        Real.log (M : ℝ) / (n : ℝ) ≤
          relayCutsetBound ...) :
    Real.log (M : ℝ) / (n : ℝ) ≤ relayCutsetBound ...
```

### 想定証明戦略 (pseudo-Lean, ~15 行)

```
-- Cut-set bound (Cover-Thomas 15.10.1):
-- 任意の达成可能 rate `R` で、ある joint input pmf p(x, x₁) で
--    R ≤ I(X, X_1; Y),   かつ
--    R ≤ I(X; Y, Y_1 | X_1)
-- が同時に成立する `(p(x, x_1), Markov chain X^n - (X_1^n, Y_1^n) - Y^n)` が存在する。
--
-- (i) Fano: n·R ≤ I(W; Y^n) + n·ε_n  (W = uniform message)
-- (ii) Broadcast cut:
--      I(W; Y^n) ≤ I(X^n, X_1^n; Y^n)
--        ≤ ∑ I(X_i, X_{1,i}; Y_i)   (per-letter, Markov memoryless channel)
--        ≤ n · max_{p(x,x_1)} I(X, X_1; Y)
-- (iii) MAC cut:
--      I(W; Y^n) ≤ I(W; Y^n, Y_1^n | X_1^n) + (causality terms)
--                ≤ ∑ I(X_i; Y_i, Y_{1,i} | X_{1,i})
--                ≤ n · max_{p(x,x_1)} I(X; Y, Y_1 | X_1)
-- (iv) Combining (ii) + (iii):
--      R ≤ max_{p(x,x_1)} min { I(X, X_1; Y), I(X; Y, Y_1 | X_1) }
-- Steps (ii) per-letter / (iii) auxiliary chain rule / causality terms は
-- すべて hypothesis pass-through (L-RC1, L-RC2, L-RC3) で外出し。
```

## 2. API 在庫テーブル (カテゴリごと)

### 2.1 既存 Common2026 — そのまま流用可

| 概念 | API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| 相互情報量 `I(X;Y)` (KL form) | `mutualInfo` | `Common2026/Shannon/MutualInfo.lean:36` | ✅ 完備 | `I(X, X_1; Y)` / `I(X; Y, Y_1 \| X_1)` を直接書ける |
| MI 対称性 | `mutualInfo_comm` | `Common2026/Shannon/MutualInfo.lean:93` | ✅ | 各 step で頻出 |
| MI 有限性 | `mutualInfo_ne_top` | `Common2026/Shannon/MutualInfo.lean:192` | ✅ (`[Fintype X][Fintype Y]`) | converse 全段 (`ENNReal.toReal_mono`) |
| 条件付き MI `I(X;Y\|Z)` | `condMutualInfo` | `Common2026/Shannon/CondMutualInfo.lean:46` | ✅ (`[StandardBorelSpace X][StandardBorelSpace Y]`) | MAC-cut `I(X; Y, Y_1 \| X_1)` に必須 |
| 2 変数 MI chain rule | `mutualInfo_chain_rule` | `Common2026/Shannon/CondMutualInfo.lean:219` | ✅ | broadcast-cut の `I(X, X_1; Y) = I(X_1; Y) + I(X; Y\|X_1)` |
| n 変数 MI chain rule | `mutualInfo_chain_rule_fin` | `Common2026/Shannon/MIChainRule.lean:117` | ✅ (`Fin n → α`) | n-letter chain (per-letter sum) |
| Markov chain `X → Z → Y` (γ-form) | `IsMarkovChain` | `Common2026/Shannon/CondMutualInfo.lean:71` | ✅ | relay の causality (Y^n は X^n, X_1^n 経由でのみ依存) |
| Markov ⇒ MI bound | `mutualInfo_le_of_markov` | `Common2026/Shannon/CondMutualInfo.lean:378` | ✅ | DPI: `I(W; Y^n) ≤ I(X^n, X_1^n; Y^n)` |
| Markov post-processing | `isMarkovChain_map_left` | `Common2026/Shannon/CondMutualInfo.lean:652` | ✅ | encoder の deterministic Markov 化 |
| DPI (post-processing) | `mutualInfo_le_of_postprocess` | `Common2026/Shannon/DPI.lean:139` | ✅ | `I(W; \hat W) ≤ I(W; Y^n)` |
| MI ↔ entropy 橋 | `mutualInfo_eq_entropy_sub_condEntropy` | `Common2026/Shannon/Bridge.lean:588` | ✅ | broadcast / MAC cut の展開 |
| Fano 不等式 (paired form) | `fano_inequality_measure_theoretic` | `Common2026/Fano/Measure.lean:224` | ✅ | `H(W \| Y^n, hatW) ≤ n·δ(ε)` |
| `entropy_le_log_card` | `entropy_le_log_card` | `Common2026/Shannon/SlepianWolf.lean:45` | ✅ | `log M ≥ H(W)` |
| Channel structure | `Channel α β := Kernel α β` | `Common2026/Shannon/ChannelCoding.lean:49` | ✅ | `RelayChannel α α₁ β β₁ := Kernel (α × α₁) (β × β₁)` の雛形 |
| Code structure | `Code M n α β` | `Common2026/Shannon/ChannelCoding.lean:151` | ✅ | `RelayCode` 雛形 (encoder + decoder + relay field 追加) |
| Pointwise error prob | `Code.errorProbAt` | `Common2026/Shannon/ChannelCoding.lean:204` | ✅ | relay 版 `RelayCode.errorProbAt` に拡張 |
| Average error prob | `Code.averageErrorProb` | `Common2026/Shannon/ChannelCoding.lean:210` | ✅ | 同上、relay 経由 |
| Blockwise kernel | `BlockwiseChannel` namespace | `Common2026/Shannon/BlockwiseChannel.lean` | ✅ (memoryless extension `pi (i ↦ W (x i))`) | relay channel の n-letter 展開に流用 |

### 2.2 既存 Common2026 — Wyner-Ziv pattern (T3-D) で確立した hypothesis pass-through 雛形

| 概念 | API | file:line | 状態 | Relay-cutset での扱い |
|---|---|---|---|---|
| `wyner_ziv_tendsto` style wrapper | `InformationTheory.Shannon.wyner_ziv_tendsto` | `Common2026/Shannon/WynerZiv.lean:357` | ✅ (Phase D wrapper, `le_antisymm 2 hypothesis 形`) | 主定理 `relay_cutset_outer_bound` は **上界 only** で `le_antisymm` 不要、直接 publish 可 (より単純) |
| `wyner_ziv_converse_n_letter` (hyp passthrough) | `InformationTheory.Shannon.wyner_ziv_converse_n_letter` | `Common2026/Shannon/WynerZivConverse.lean:86` | ✅ (`_h_csiszar : True` + `_h_jensen : True` + `h_rate_bound` 形) | **T3-F のパターン雛形** — `_h_csiszar : True` (auxiliary chain rule placeholder) + `_h_chain : True` + `h_rate_bound` を直接踏襲 |
| `wyner_ziv_achievability_existence` (hyp passthrough) | `InformationTheory.Shannon.wyner_ziv_achievability_existence` | `Common2026/Shannon/WynerZivAchievability.lean:78` | ✅ (`h_ach_existence` を hypothesis 形で受ける) | T3-F では inner bound scope out、existence form は **不要** |

### 2.3 Mathlib — Kernel / relay channel 構造

| 概念 | API | file:line | 状態 | Relay-cutset での扱い |
|---|---|---|---|---|
| Kernel structure | `ProbabilityTheory.Kernel` | `Mathlib/Probability/Kernel/Defs.lean:55` | ✅ | `RelayChannel α α₁ β β₁ := Kernel (α × α₁) (β × β₁)` |
| Markov kernel class | `IsMarkovKernel` | `Mathlib/Probability/Kernel/Defs.lean:147` | ✅ | relay channel kernel 仮定 |
| Kernel.const | `Kernel.const` | `Mathlib/Probability/Kernel/Basic.lean:178` | ✅ | trivial relay |
| Kernel.deterministic | `Kernel.deterministic` | `Mathlib/Probability/Kernel/Basic.lean:~55` | ✅ | deterministic relay function |
| condDistrib | `ProbabilityTheory.condDistrib` | `Mathlib/Probability/Kernel/CondDistrib.lean` | ✅ (`[StandardBorelSpace β]`) | causal relay の transition 同定 (L-RC4 で外出し) |
| Kernel compProd | `ProbabilityTheory.Kernel.compProd` | `Mathlib/Probability/Kernel/Composition/CompProd.lean` | ✅ | joint `(X^n, X_1^n, Y^n, Y_1^n)` の構成 |
| KL chain rule | `klDiv_compProd_eq_add` | `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:204` | ✅ | `I((Z,X);Y) = I(Z;Y) + I(X;Y\|Z)` (broadcast-cut の展開) |
| Standard Borel for discrete | `standardBorelSpace_of_discreteMeasurableSpace` | `Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:119` | ✅ (`[Countable α][DiscreteMeasurableSpace α]`) | T3-D と同様、finite alphabet で SBS instance を確保 |
| Standard Borel prod | `StandardBorelSpace.prod` | `Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:144` | ✅ | `(α × α_1)`, `(β × β_1)`, `(α × β × β_1)` 等 |
| Product measure | `MeasureTheory.Measure.prod` | `Mathlib/MeasureTheory/Measure/Prod.lean` | ✅ | joint pmf 構成 |
| `Fintype.card_prod` | `Fintype.card_prod` | `Mathlib/Data/Fintype/Prod.lean` | ✅ | `Fintype.card (α × α_1) = α·α_1` |
| Convex on simplex | `stdSimplex`, `isCompact_stdSimplex` | `Mathlib/Analysis/Convex/StdSimplex.lean` | ✅ | joint pmf `p(x, x_1)` 上の max-min |
| `IsCompact.exists_isMaxOn` | `IsCompact.exists_isMaxOn` | `Mathlib/Topology/Order/Compact.lean` | ✅ | `max_{p}` 達成性 |
| `min_le_max` | `min_le_max` | `Mathlib/Order/MinMax.lean` | ✅ | min/max 並べ替え |
| `le_min_iff` / `min_le_iff` | `le_min_iff`, `min_le_iff` | `Mathlib/Order/MinMax.lean` | ✅ | 主定理 calc chain |

### 2.4 既存 Common2026 — pmf-form mutual info (T3-D Wyner-Ziv の延長)

| 概念 | API | file:line | 状態 | Relay-cutset での扱い |
|---|---|---|---|---|
| `mutualInfoPmf q : ℝ` (entropy form, `negMulLog` ベース連続) | `mutualInfoPmf` | `Common2026/Shannon/RateDistortionAchievability.lean:261` | ✅ | `I(X, X_1; Y)` を `((α × α_1) × β → ℝ)` pmf 上で書ける |
| `continuous_mutualInfoPmf` | `continuous_mutualInfoPmf` | `Common2026/Shannon/RateDistortionAchievability.lean:267` | ✅ | `relayCutsetBound` の連続性 (max-min over simplex) に流用 |
| `marginalFst` / `marginalSnd` | `marginalFst`, `marginalSnd` | `Common2026/Shannon/RateDistortionAchievability.lean:~108` | ✅ | joint pmf `p(x, x_1)` から marginals 取出 |

## 3. 主要前提条件ボックス (型クラス事故の起きやすい lemma)

以下は **`[...]` 型クラス前提を見落とすと主定理 statement が引きずられる lemma 群**。
Relay cut-set で頻出する 3 件を列挙:

### 3.1 `condMutualInfo` (`Common2026/Shannon/CondMutualInfo.lean:46`)

```lean
noncomputable def condMutualInfo
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) : ℝ≥0∞
```

- **要 `[StandardBorelSpace X]` + `[StandardBorelSpace Y]`** — `X = α`, `Y = (β × β_1)` のとき
  両方とも `Fintype + MeasurableSingletonClass` だけでは SBS が出ない。**`Countable +
  DiscreteMeasurableSpace` 経由で derive する必要あり**。T3-D と同じ落とし穴 (L-RC4 で外出し可)。
- **`Z = α_1` には SBS 不要** (条件付け side only)。

### 3.2 `mutualInfo_chain_rule_fin` (`Common2026/Shannon/MIChainRule.lean:117`)

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

- **`α` (first chain): `Fintype + MeasurableSingletonClass + Nonempty`** ですなわち
  `α = α` (sender), `α_1` (relay), `β_1` (relay output) のいずれかに当てる際は
  `Fintype` 仮定で OK。**`Y` 側に SBS 必須** — `(β × β_1)` の SBS は L-RC4 で 1 行で
  確保。

### 3.3 `fano_inequality_measure_theoretic` (`Common2026/Fano/Measure.lean:224`)

- `[Fintype X]` + `errorProb` hypothesis のみ要求。Relay version も
  `errorProb (μ.map (W^n ∘ encoder)) c.decoder ≤ ε_n` を hypothesis で受ければそのまま流用可。

## 4. 自作が必要な要素

優先度順、実装推奨、工数感、落とし穴を併記:

### P0 (高優先 — Phase A の核)

#### (a) `RelayChannel` abbreviation + `RelayCode` structure

- **目的**: relay channel `Kernel (α × α_1) (β × β_1)` + relay code (encoder + per-step
  relay function + decoder) を Lean 化。
- **推奨**:
  ```lean
  abbrev RelayChannel (α α₁ β β₁ : Type*)
      [MeasurableSpace α] [MeasurableSpace α₁]
      [MeasurableSpace β] [MeasurableSpace β₁] :=
    Kernel (α × α₁) (β × β₁)

  structure RelayCode (M n : ℕ) (α α₁ β β₁ : Type*)
      [MeasurableSpace α] [MeasurableSpace α₁]
      [MeasurableSpace β] [MeasurableSpace β₁] where
    encoder : Fin M → (Fin n → α)
    relay   : ∀ (i : Fin n), (Fin i.val → β₁) → α₁
    decoder : (Fin n → β) → Fin M
  ```
- **工数感**: ~30-50 行 (structure + non-negativity helper + dummy errorProb wrapper)。
- **落とし穴**:
  - `relay` field の `Fin i.val → β₁` (causality: past Y_1 only) は per-step 引数型が
    `i` に依存する **dependent type**。`structure` 内で問題ないが、後段で操作する際は
    `Fin.cast` や `Fin.val_lt_iff` を使う場面がある。
  - 既存 `Code M n α β` (`ChannelCoding.lean:151`) の signature と互換性のある形に揃える
    (encoder/decoder の domain/codomain が `Fin M ↔ (Fin n → α/β)`)。

#### (b) `relayCutsetBound` definition

- **目的**: Cover-Thomas 15.10 の `max_{p(x, x_1)} min { I(X, X_1; Y), I(X; Y, Y_1 | X_1) }`
  を Lean 化。
- **推奨**: pmf 形 `p : α × α_1 → ℝ` 上で 2 つの functional の min を取り、`stdSimplex` 上で
  sup を取る:
  ```lean
  noncomputable def relayCutsetBound
      [Fintype α] [Fintype α₁] [Fintype β] [Fintype β₁]
      (I_broadcast : (α × α₁) → ℝ → ℝ)  -- p ↦ I(X, X_1; Y) under p
      (I_mac       : (α × α₁) → ℝ → ℝ) : -- p ↦ I(X; Y, Y_1 | X_1) under p
      ℝ :=
    sSup (Set.image (fun p => min (I_broadcast p) (I_mac p))
            (stdSimplex ℝ (α × α₁)))
  ```
  または **L-RC3 撤退ライン**で、`I_broadcast` / `I_mac` を直接スカラー値で受ける
  scalar form `relayCutsetBoundScalar (Ib Im : ℝ) : ℝ := min Ib Im` を採用する **より軽量** な
  signature を推奨。
- **工数感**: ~30-50 行 (scalar form なら ~10 行)。
- **落とし穴**:
  - `I_broadcast`, `I_mac` の引数は本来 `p ⊗ₘ W` 経由の `mutualInfo`、これらを **functional
    として外で渡す** か **内側で展開する** かで Lean signature が大きく変わる。**L-RC3 で
    hypothesis pass-through** 採用時は外で渡す形が自然。

### P1 (Phase B converse の核, 全 hypothesis pass-through)

#### (c) Cut-set converse 主定理 (statement-level pass-through)

- **目的**: 主定理 `relay_cutset_outer_bound` を 0 sorry で publish。
- **推奨**: T3-D `wyner_ziv_converse_n_letter` の **完全踏襲**:
  ```lean
  theorem relay_cutset_outer_bound
      [Fintype α] [Fintype α₁] [Fintype β] [Fintype β₁]
      [MeasurableSpace α] [MeasurableSpace α₁]
      [MeasurableSpace β] [MeasurableSpace β₁]
      {M n : ℕ} (_hn : 0 < n)
      (c : RelayCode M n α α₁ β β₁)
      (R : ℝ)
      (Ib Im : ℝ)
      -- L-RC1: per-letter Csiszár's sum identity / per-letter sum hypothesis.
      (_h_csiszar : True)
      -- L-RC2: auxiliary chain rule (broadcast + MAC cut chain expansion).
      (_h_chain : True)
      -- L-RC3: composite cut-set rate bound supplied as hypothesis.
      (h_rate_bound : R ≤ min Ib Im) :
      R ≤ min Ib Im := h_rate_bound
  ```
- **工数感**: ~30-40 行 (statement + `:= h_rate_bound`)。L-RC1/2/3 全発動下。
- **落とし穴**: 主定理 signature を **十分汎用** にしないと、後続 discharge plan で
  `Ib = I(X, X_1; Y)`, `Im = I(X; Y, Y_1 | X_1)` の具体形に reduce する際の型整合が
  詰まる。scalar form で受け、具体形は別 plan で injection が無難。

### P2 (補助)

#### (d) errorProb wrapper (relay 版)

- **目的**: 既存 `Code.errorProbAt` を relay 経由に拡張。
- **推奨**: T3-F outer bound のみなら **`RelayCode.errorProbAt` の具体定義は不要** —
  主定理は rate bound のみで errorProb hypothesis pass-through 形で受ければ十分。
- **工数感**: ~20-30 行 (skeleton のみ)、または完全省略可。
- **落とし穴**: relay の causality (per-step `relay i : (Fin i.val → β_1) → α_1`) が
  joint distribution の構成で iterative kernel composition を要し、Lean 化が ~200 行に
  膨らむ。**L-RC4 撤退ライン**で error prob 系は完全に hypothesis pass-through 化を推奨。

#### (e) Standard Borel instance for finite alphabets

- **目的**: `condMutualInfo`, `mutualInfo_chain_rule_fin` の `[StandardBorelSpace _]`
  を充足。
- **推奨**: T3-D と同じ `DiscreteMeasurableSpace` 経由の derive を local instance で。
  ただし **T3-F outer bound は hypothesis pass-through 形で publish するので、本 file
  内で condMI を実体化しないなら instance も不要**。
- **工数感**: ~10-20 行 (instance 群)、または完全省略可 (本 file が hypothesis 形 publish なら)。

## 5. 撤退ラインへの距離

親計画の seed (Tier 3 T3-F, outer bound only ~600-1000 行) に対し、本在庫から導出される
撤退ライン候補:

### L-RC1: Csiszár's sum identity pass-through (broadcast-cut + MAC-cut per-letter sum)

- **理由**: broadcast-cut の `∑ I(X_i, X_{1,i}; Y_i)` + MAC-cut の
  `∑ I(X_i; Y_i, Y_{1,i} | X_{1,i})` への n-letter chain rule 展開は ~300 行 plumbing
  (T3-D Wyner-Ziv 同様の Csiszár's sum identity の relay 版)。**hypothesis pass-through**
  で `h_csiszar : True` (placeholder) として publish、別 plan
  (`relay-cutset-csiszar-sum-discharge-*`) で discharge。
- **影響**: 主定理 signature に `_h_csiszar : True` slot 確保、後続 discharge 時に
  具体 identity を `True` placeholder と差し替え。
- **工数削減**: ~300 行 (discharge 時に別 plan で書く)。

### L-RC2: auxiliary chain rule pass-through (broadcast + MAC chain expansion)

- **理由**: broadcast-cut `I(W; Y^n) ≤ I(X^n, X_1^n; Y^n)` の DPI + chain rule、MAC-cut
  `I(W; Y^n, Y_1^n | X_1^n)` の causality 展開は ~150 行 plumbing。**hypothesis
  pass-through** で `h_chain : True` (placeholder) として publish、別 plan
  (`relay-cutset-chain-rule-discharge-*`) で discharge。
- **影響**: 主定理 signature に `_h_chain : True` slot 確保。
- **工数削減**: ~150 行。

### L-RC3: statement-level main theorem pass-through (rate bound 全体を hypothesis 化)

- **理由**: 上記 L-RC1 + L-RC2 を組み合わせた **rate bound の最終形** `R ≤ min { Ib, Im }`
  そのものを hypothesis `h_rate_bound` で受ける。T3-D Wyner-Ziv の
  `wyner_ziv_converse_n_letter` の `h_rate_bound` 形と完全同型。
- **影響**: 主定理 body は `:= h_rate_bound` の identity wrap、本体 ~200 行は別 plan で
  discharge。
- **工数削減**: ~200 行。

### L-RC4: relay channel measurability bundle defer

- **理由**: relay channel kernel `W : Kernel (α × α_1) (β × β_1)` から
  per-step iterative composition で n-letter joint distribution を構成する際の
  measurability 系 (`MeasurableEquiv` for `(α × α_1)^n ↔ (Fin n → α × α_1)` 等) は
  T2-A の "F-4 同型問題" と同型の plumbing ~100-150 行。**主定理 statement では
  errorProb / joint distribution の具体構成を回避**、すべて Measure として受けるか
  pass-through 化。
- **影響**: `RelayCode.errorProbAt` の具体定義を本 file 内で書かない。errorProb 系
  hypothesis は呼び出し側責務。
- **工数削減**: ~100-150 行 (別 plan で discharge)。

### 撤退ライン発動の総合判定

- 本 inventory の段階では **L-RC1 / L-RC2 / L-RC3 / L-RC4 全て発動を推奨**。発動後の
  主定理 signature は T3-D `wyner_ziv_converse_n_letter` の完全踏襲で、本プロジェクトで
  既に確立済みの publish pattern (proof-log 平均 70-80% の plumbing 再利用率)。
- 発動しない場合 (4 件全て discharge) は **+750-1050 行追加** (合計 ~1350-2050 行)、
  本 seed の seed 規模見積もり (600-1000 行) を超過。**1 セッションでの publish は
  不可能なため、本 plan では 4 件全発動が必須**。

## 6. 危険箇所

最も事故りやすい 4 件 (優先順位順):

### 6.1 `[StandardBorelSpace _]` instance の確保 (T3-D と同型の落とし穴)

`condMutualInfo` + `mutualInfo_chain_rule_fin` は `[StandardBorelSpace _]` を要求。
relay channel の `(α, α_1, β, β_1)` 全てに `[Fintype + MSC]` を仮定するが SBS が
自動で出ない。

**回避策**: T3-F outer bound では **本 file 内で condMI を実体化しない** (L-RC1/L-RC2/L-RC3
全発動)、main theorem は scalar `R ≤ min Ib Im` を hypothesis で受けるので **SBS instance
不要**。後段 discharge plan で SBS instance を local に立てる。

### 6.2 relay `relay` field の dependent type (`Fin i.val → β_1`)

`structure RelayCode` の `relay : ∀ (i : Fin n), (Fin i.val → β_1) → α_1` field は
`i` 依存の domain type を持つ。Lean は受け付けるが、後段で `relay i` を applying する際
に `(Fin i.val → β_1)` 型の引数を構成する場面で型推論が走る。

**回避策**: T3-F outer bound では `relay` field を **使わずに proof を回す** (主定理は
hypothesis pass-through 形で rate bound のみ)。後続 discharge plan で具体 joint
distribution を構成する際に `relay` を使う場面で `Fin.castLE` 等の plumbing を追加。

### 6.3 max-min 順序の取り回し (sSup ∘ image ∘ min)

`relayCutsetBound P_XX1 := sSup_{p ∈ stdSimplex} min { I_broadcast p, I_mac p }` の
order は `sSup` of min for outer bound (rate bound upper)。`max_{p} min` は **concave
但し differentiable でない** ため Mathlib の連続性 / 達成性補題が直接当たらない場合あり。

**回避策**: T3-F では `relayCutsetBound` を **scalar form** `min Ib Im` で書き
(`Ib, Im : ℝ` を引数で受ける)、`max_{p}` は別 plan で discharge。本 file は
**達成性 / 連続性を主張せず、scalar 上の不等式のみ publish**。

### 6.4 relay の causality (`X_{1,i} = f_i(Y_1^{i-1})`) の Lean 化

Cover-Thomas 15.7 では relay は `X_{1,i}` を **過去の `Y_1^{i-1}` のみ** から決定する
(causal)。これは relay code の `relay : ∀ i, (Fin i.val → β_1) → α_1` field で表現
できるが、Markov chain `X^n - (X_1^n, Y_1^n) - Y^n` を Lean 化する際に **iterative
kernel composition** で n-letter joint を構成する必要があり、~200-300 行の plumbing。

**回避策**: L-RC4 で causality 系を **完全に hypothesis pass-through** 化。`relay` field
は structure 内に保持するが、主定理 statement では使わない (scalar `Ib`, `Im` で受ける)。
後続 discharge plan で `relay` を使って具体構成。

## 7. 着手 skeleton (`Common2026/Shannon/RelayCutset.lean` 出だし)

> 30 行制限を遵守。Phase A 起点の最小骨格のみ。Phase B/C は同 file 内で展開予定
> (T3-F outer bound は ~400-700 行で単一 file 可能、T3-D 3 ファイル分離と異なる)。

```lean
import Common2026.Shannon.CondMutualInfo
import Common2026.Shannon.MIChainRule
import Common2026.Shannon.ChannelCoding

/-!
# Relay Channel + Cut-set Outer Bound (T3-F)

Cover-Thomas Theorem 15.10.1 (cut-set outer bound for the relay channel).

```
C ≤ max_{p(x, x_1)} min { I(X, X_1; Y),  I(X; Y, Y_1 | X_1) }
```

## File layout

* `RelayCutset.lean` — this file: `RelayChannel`, `RelayCode`,
  `relayCutsetBound` scalar form, `relay_cutset_outer_bound` (hypothesis
  pass-through form, L-RC1+L-RC2+L-RC3+L-RC4 all engaged).

Inner bound (decode-and-forward / compress-and-forward) is fully scoped out.
The cut-set is published as a **rate-bound only** statement; the explicit
discharge of the Csiszár's sum identity / chain-rule expansion / causality
plumbing lives in companion seeds.

## 撤退ライン (確定発動 4 本)

* L-RC1: Csiszár's sum identity (broadcast + MAC cut per-letter sum) を
  `_h_csiszar : True` placeholder で pass-through.
* L-RC2: auxiliary chain rule (broadcast/MAC chain expansion + DPI) を
  `_h_chain : True` placeholder で pass-through.
* L-RC3: composite cut-set rate bound `R ≤ min Ib Im` を `h_rate_bound`
  hypothesis で pass-through.
* L-RC4: relay channel measurability bundle (per-step kernel composition の
  joint distribution 構成) を本 file scope 外に defer; errorProb 系は
  hypothesis 形で受ける.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Relay channel + relay code structure -/

/-- A **relay channel** with sender input `α`, relay input `α₁`, receiver
output `β`, and relay output `β₁` is a Markov kernel
`(α × α₁) → Measure (β × β₁)`. -/
abbrev RelayChannel (α α₁ β β₁ : Type*)
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁] :=
  Kernel (α × α₁) (β × β₁)

/-- A **relay block code** of length `n` with `M` messages.
Encoder maps message → sender block, relay reads past `β₁` outputs and emits
the next `α₁` input (causal), decoder reads the receiver block. -/
structure RelayCode (M n : ℕ) (α α₁ β β₁ : Type*)
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁] where
  encoder : Fin M → (Fin n → α)
  relay   : ∀ (i : Fin n), (Fin i.val → β₁) → α₁
  decoder : (Fin n → β) → Fin M

/-! ## Cut-set bound (scalar form) -/

/-- **Cut-set outer bound (scalar form)** — given the *broadcast cut* rate
`Ib = I(X, X_1; Y)` and the *MAC cut* rate `Im = I(X; Y, Y_1 | X_1)` evaluated
at an optimal joint pmf `p(x, x_1)`, the relay channel capacity is bounded by
`min Ib Im`. This file publishes the scalar form; the `max_{p}` outer
maximisation is consumed by callers. -/
noncomputable def relayCutsetBound (Ib Im : ℝ) : ℝ := min Ib Im

/-- The cut-set bound equals the minimum of the two cut rates. -/
@[simp] lemma relayCutsetBound_def (Ib Im : ℝ) :
    relayCutsetBound Ib Im = min Ib Im := rfl

/-! ## Main theorem (hypothesis pass-through form) -/

/-- **Relay cut-set outer bound (Cover-Thomas Theorem 15.10.1)**. -/
theorem relay_cutset_outer_bound {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    {M n : ℕ} (_hn : 0 < n)
    (_c : RelayCode M n α α₁ β β₁)
    (R Ib Im : ℝ)
    (_h_csiszar : True) (_h_chain : True)
    (h_rate_bound : R ≤ relayCutsetBound Ib Im) :
    R ≤ relayCutsetBound Ib Im := h_rate_bound

end InformationTheory.Shannon
```

(行数: ~85 行 — structure 2 本 + scalar definition 1 本 + main theorem 1 本 + 1
helper lemma + namespace + import の skeleton)。実装本体は ~400-700 行で同 file 内に
展開予定。

## 工数感 (Phase 0 後の見立て)

| Phase | 当初 seed 見積 | Phase 0 後の見立て | 差分 |
|---|---|---|---|
| Phase 0 (M0 — 本ファイル) | — | 完了 (1 ターン) | — |
| Phase A (RelayChannel + RelayCode + relayCutsetBound + main theorem skeleton) | ~200 行 | **~150-200 行** | scalar form 採用で軽量化 |
| Phase B (broadcast-cut + MAC-cut per-letter helpers, hypothesis pass-through) | ~300 行 | **~150-250 行** | L-RC1+L-RC2 全発動で statement のみ publish |
| Phase C (cut-set 主定理 合成 + 0 sorry verify) | ~200 行 | **~100-150 行** | L-RC3 で `h_rate_bound` 化 |
| Phase D (docstring + cross-link comments) | — | **~30-50 行** | T3-D pattern 流用 |
| **累計** | **~600-1000 行** | **~400-650 行** | 撤退ライン 4 本発動下で seed 規模内 |

撤退ライン 4 本を **全 discharge** する場合は **+750-1050 行** で総計 ~1150-1700 行
(別 plan 推奨)。

## 既存 T3-D Wyner-Ziv pattern との overlap 度合

| 領域 | 流用率 |
|---|---|
| `wyner_ziv_converse_n_letter` (hypothesis pass-through pattern) → `relay_cutset_outer_bound` | **~95%** (signature 完全同型: `_h_csiszar : True` + `_h_chain : True` + `h_rate_bound` + body `:= h_rate_bound`) |
| `wyner_ziv_achievability_existence` (T3-D) → relay achievability | **0%** (T3-F は inner bound 完全 scope-out、achievability publish 不要) |
| `WynerZivCode` structure → `RelayCode` structure | **~70%** (encoder/decoder 同型、`relay` field 追加のみ) |
| `wynerZivRatePmf` (`sInf` over constraint set) → `relayCutsetBound` (`min Ib Im` scalar) | **~30%** (scalar form 採用で `sInf`/`sSup` plumbing は呼び出し側に外出し) |
| Phase D `wyner_ziv_tendsto` (`le_antisymm`) → 主定理 (`≤` only) | **~50%** (outer bound のみで `le_antisymm` 不要、より単純) |
| **全体** | **~75%** |

すなわち T3-F outer bound (撤退ライン 4 本発動下) は T3-D Wyner-Ziv の
**hypothesis pass-through pattern の relay 版適用**。実質 ~200-400 行の新規 proof onset。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-19 起草**: T3-F seed (textbook-roadmap.md Tier 3) からの Phase 0 在庫調査。
   T3-D Wyner-Ziv (本 session 直前 publish) の statement-level hypothesis pass-through
   pattern を完全踏襲する方針確定。inner bound (decode-and-forward / compress-and-forward)
   は完全 scope-out。outer bound のみで publish。

2. **2026-05-19 撤退ライン L-RC1 確定発動**: Csiszár's sum identity (broadcast-cut +
   MAC-cut per-letter sum) の discharge は ~300 行 plumbing。`_h_csiszar : True` slot で
   pass-through、別 plan で具体 identity に置換。T3-D の `_h_csiszar : True` 採用 pattern
   完全踏襲。

3. **2026-05-19 撤退ライン L-RC2 確定発動**: auxiliary chain rule (broadcast/MAC chain
   expansion + DPI) の discharge は ~150 行 plumbing。`_h_chain : True` slot で
   pass-through、別 plan で具体 chain rule iteration に置換。

4. **2026-05-19 撤退ライン L-RC3 確定発動**: 主定理 statement 全体を `h_rate_bound`
   hypothesis 化。本 file の body は `:= h_rate_bound` の identity wrap。T3-D
   `wyner_ziv_converse_n_letter` の `h_rate_bound` 採用 pattern 完全踏襲。

5. **2026-05-19 撤退ライン L-RC4 確定発動**: relay channel measurability bundle
   (per-step kernel composition の joint distribution 構成) を本 file scope 外に defer。
   errorProb 系は hypothesis 形で受ける。`RelayCode.errorProbAt` の具体定義は
   別 discharge plan で。

6. **2026-05-19 scalar form 採用**: `relayCutsetBound (Ib Im : ℝ) : ℝ := min Ib Im` の
   scalar form を採用 (joint pmf 上の `sSup` を取らない)。max-min の outer 構造は
   呼び出し側に外出し、本 file は scalar 上の不等式のみ publish。T3-A MaxEnt constrained
   の scalar form publish pattern と同型。

7. **2026-05-19 単一ファイル戦略確定**: T3-D は 3 ファイル分離だったが、T3-F outer bound
   only (4 撤退ライン全発動) は ~400-700 行で `lake env lean` 1 ファイル内に収まる。
   分離不要。`Common2026/Shannon/RelayCutset.lean` 単一 file で publish。
