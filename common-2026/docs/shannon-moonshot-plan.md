# Shannon ムーンショット計画 🌙

> **Status (2026-05-10): 🌙 ムーンショット達成 (Phase 4-γ 完了)**。`Common2026/Shannon/Converse.lean` で `shannon_converse_single_shot` が sorry ゼロで通過。Phase 4-M0 〜 γ の全段が活性。インベントリは [`docs/shannon-mathlib-inventory.md`](shannon-mathlib-inventory.md)、最終振り返りは [Phase 4-γ 結果](#phase-4-γ-結果-2026-05-10) 節を参照。
> Fano ムーンショット ([fano-moonshot-plan.md](fano-moonshot-plan.md)) の Phase 3 達成を前提とする後継プロジェクト。
> ゴールは「Mathlib に既存の `klDiv` を主軸に、mutual information / data processing inequality / Shannon converse を接続する」こと。

## Context

### モチベーション（重要）

Fano プロジェクトと同じく、第一義の目標は **Mathlib への upstream PR ではない**。

> 「Mathlib に未実装の定理を、門外漢の人間が Claude Code にどこまで証明してもらえるか」を試し、
> **形式化のコストがいかに安くなったか**を世界に対して示すこと。

各 Phase で `proof-log` skill と `scripts/session_metrics.ts` から metrics を取り、Fano プロジェクトの 4 段（Phase 0〜3）と並べて **「KL chain rule 主軸の plumbing は binEntropy 凹性主軸より速かったか / 遅かったか」** の定量比較を出すのがデモの中核資産。

### 現状

- **Mathlib 側**: `klDiv (μ ν : Measure α) : ℝ≥0∞` (`Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57`) が既存。`klDiv_compProd` 系の chain rule もある (`Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean`)。
- **Mathlib 側の不在** (Fano Phase 2 で確認済み): mutual information, conditional mutual information, DPI、Shannon の通信路符号化定理 converse、いずれも無し。`Mathlib/InformationTheory/` ディレクトリの中身は KL + Hamming + 符号理論のみで、Shannon 系の中核がぽっかり空いている。
- **我々の側**: `Common2026/Fano/Measure.lean` で測度論版 Fano (X Fintype, Y 任意可測, deterministic decoder) が完成。`condEntropy` / `errorProb` / `pointwiseErrorProb` を自前定義済み。

つまり「**Mathlib の klDiv と、我々の Phase 3 condEntropy が並走しているが、両者をつなぐ MI / DPI が空白**」の状態。Phase 4 はこの空白を埋める。

### ムーンショット = single-shot Shannon converse

最終到達点:

```lean
theorem shannon_converse_single_shot
    {M X Y : Type*} [Fintype M] [Fintype X] [DecidableEq M] [Nonempty M]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y]
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → X) (Yo : Ω → Y) (decoder : Y → M)
    (hMsg : Measurable Msg) (hYo : Measurable Yo)
    (hencoder : Measurable encoder) (hdecoder : Measurable decoder)
    (hMsg_uniform : μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    -- Markov: Msg → encoder ∘ Msg → Yo → decoder ∘ Yo
    (hMarkov : ⟨…⟩)
    (hcard : 2 ≤ Fintype.card M) :
    Real.log (Fintype.card M) ≤
      (mutualInfo μ (encoder ∘ Msg) Yo).toReal +
        Real.binEntropy (errorProb μ Msg (decoder ∘ Yo)) +
        errorProb μ Msg (decoder ∘ Yo) * Real.log ((Fintype.card M : ℝ) - 1)
```

要は「rate `R := log|M|` に対し `R ≤ I(X;Y) + h(Pe) + Pe · log(|M|-1)`」。これを変形すれば、`I(X;Y) < R` なら `Pe` は 0 から離れる、という Shannon converse の典型形になる。

### 非ゴール

- **ブロック符号 / `n → ∞` 漸近 (single-letterization)**: `I(X^n; Y^n) ≤ n · C` の積構造とブロック化 — Phase 5 として切り出す。Phase 4 は **single-shot** で閉じる
- **Channel capacity `C := sup_{P_X} I(X;Y)`**: sup の取り扱いと最大化 — converse は単一 `(P_X, P_Y)` 対で書ける
- **Achievability (random coding / typicality)**: 反対側の半分は別ムーンショット
- **Mathlib upstream PR**: 副産物として出るのは歓迎、能動的には追わない

---

## Approach

**3 段階構成 (Phase 4-M0 → α → β → γ)。Mathlib の `klDiv` を主軸とし、Phase 3 の `condEntropy` は補助役として共存させる。**

```
Phase 4-M0  : Mathlib KL API 在庫調査 (1 ターン)        ← Phase 2 と同型の subagent 並列調査
              ─────────────────────────────────────
Phase 4-α   : mutualInfo + 基本性質 + DPI               ← 山場。klDiv_compProd を主役にする
              ─────────────────────────────────────
Phase 4-β   : Phase 3 condEntropy との bridge           ← X Fintype で I(X;Y) = H(X) - H(X|Y)
              ─────────────────────────────────────
Phase 4-γ   : single-shot Shannon converse              ← Fano + DPI + bridge の組み合わせ
              （ムーンショット 🌙）
```

### Approach の根幹: KL chain rule を主役にする

Fano Phase 3 では `binEntropy` 凹性 + Bochner Jensen を主役にした。Phase 4 では **`klDiv_compProd_eq_add` (chain rule)** を主役にする。

```
KL(μ ⊗ κ ‖ ν ⊗ η) = KL(μ ‖ ν) + KL(μ ⊗ κ ‖ μ ⊗ η)
```

(`Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:204`、measurability 仮定なし、ℝ≥0∞ 値)

ここから次のものが構造的に出てくる:

- **DPI**: kernel `f` を片側にだけ適用して `KL(f_*μ ‖ f_*ν) ≤ KL(μ ‖ ν)`。MI に翻訳すると `I(X; f(Y)) ≤ I(X; Y)`
- **MI chain rule**: `I(X; Y, Z) = I(X; Y) + I(X; Z | Y)`
- **MI と独立性**: `I(X; Y) = 0 ↔ X ⫫ Y`

つまり「**klDiv chain rule から構造的に出てくるもの**」を順番に取り出すのが Phase 4 の基本動作。新規の凹性 Jensen は Phase 3 で組み終わっているので、Phase 4 では発生しないはず（と現時点では予想）。

**M0 後の追加事項 (2026-05-09)**:
- Mathlib にあるのは `Kernel.compProd` 形 (`⊗ₘ`) のみで、**`Measure.prod` 形 (`mutualInfo` 定義の右辺)** との橋渡し補題は不在
  → 最初に **`klDiv_prod_eq_klDiv : klDiv (μ.prod ν₁) (μ.prod ν₂) = klDiv ν₁ ν₂`** を `Measure.prod = · ⊗ₘ Kernel.const _ ·` 経由で `klDiv_compProd_left` (`@[simp]`) から導出する
- DPI 直接補題 (`klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν`) も不在
  → `Kernel.deterministic f` で `f` を kernel 化し、`compProd_map_condDistrib` で disintegrate して chain rule に乗せる戦略で自作

### なぜ 3 段に分けるか

1. **Phase 4-α だけで成果が立つ**。「Mathlib の `klDiv` に Shannon の MI と DPI を接続した」だけで `Common2026/Shannon/MutualInfo.lean` が生まれ、proof-log が取れる。Phase 4-γ に届かなくても価値が残る
2. **Phase 4-β は Phase 3 を捨てない選択**。Phase 3 の半離散 `condEntropy` は Phase 4-α の `mutualInfo` に意味的には subsume されるが、bridge を書くことで「両形式が同値」を明示し、Phase 1〜3 の蓄積を活用する
3. **Phase 4-γ は組み合わせのみ**。新規補題は最小限で、Phase 3 Fano + Phase 4-α DPI + Phase 4-β bridge から 50〜100 行で converse を導ける見込み

### ファイル構成 (Phase 4 終了時)

```
Common2026/
  Fano/                          ← Phase 0〜3 の蓄積。不変
    Core.lean / DPI.lean / Measure.lean / ...
  Shannon/                       ← Phase 4 の新設名前空間
    MutualInfo.lean              ← Phase 4-α: 定義 + 基本性質
    DPI.lean                     ← Phase 4-α: data processing inequality
    Bridge.lean                  ← Phase 4-β: Phase 3 condEntropy との橋渡し
    Converse.lean                ← Phase 4-γ: single-shot Shannon converse
```

`Common2026.lean` (library root) に対応する `import Common2026.Shannon.*` を順次追記。

---

## Phase 4-M0: Mathlib KL API 在庫調査

### スコープ

Phase 2 (Fano) と同型の subagent 並列調査。**1 ターンで完走する想定**。Phase 4-α 着手前に plumbing 量と撤退リスクを可視化する。

### 調査軸 (subagent 並列、Phase 2 のテンプレートを再利用)

| 軸 | 確認したい API | 期待される存否 |
|---|---|---|
| KL の chain rule | `klDiv_compProd`, `klDiv_chainRule_*` | ✅ 既存 (要 signature 確認) |
| KL の DPI / monotonicity | `klDiv_le_klDiv_of_*`, `klDiv_map_le` 系 | 不明。最重要調査軸 |
| KL と product measure | `klDiv (μ.prod ν) (μ' .prod ν')` の和分解、独立性同値 | 不明 |
| `Measure.map` 下の klDiv | pushforward での KL 不変 / 単調 | 不明 |
| KL の対称化 / fDivergence | Mathlib の `fDivergence` 系統との関係 | 不明 |
| `IndepFun` API | mutualInfo = 0 ↔ 独立 を書くために | ✅ 既存 (Phase 2 で確認) |

### 成果物

- `docs/shannon-mathlib-inventory.md` — 上の表の調査結果 + Phase 4-α で使える KL 補題リスト + 自作項目
- 計画書 ([このファイル](shannon-moonshot-plan.md)) への調査結果反映 (主に Approach 節と Phase 4-α 節)

### Done 条件

- 「Phase 4-α で必要な KL 補題のうち X% が Mathlib 既存」と一文で言える状態
- Phase 4-α の skeleton (`Common2026/Shannon/MutualInfo.lean` の出だし) が書ける状態

### 工数感

1 ターン (10〜15 分)。Fano Phase 2 と同じ規模。

### Phase 4-M0 結果 (2026-05-09)

- **完了**: subagent 3 並列 (chain rule + DPI / product + map / fDivergence + IndepFun + Kernel) → `docs/shannon-mathlib-inventory.md` に統合
- **既存率**: 「素材」(klDiv 定義 / chain rule / klDiv_eq_zero_iff / IndepFun ↔ map prod / condDistrib / Kernel.deterministic) は **100%**。「主役定理」(mutualInfo / DPI / KL × Measure.prod 分解) は **0%** で全自作
- **撤退ライン判定**: 「DPI / monotonicity が驚くほど未整備」に **軽く触れている**。直接の DPI 補題は完全不在だが、`klDiv_compProd_eq_add` + `Kernel.deterministic` 経由で導出可能な見通し
- **Phase 4-α への影響**:
  - `mutualInfo` 定義 + `mutualInfo_nonneg` + `mutualInfo_comm` + `mutualInfo_eq_zero_iff_indep` の 4 項目は **plumbing 1〜2 日見込み** (素材完備)
  - **DPI が最大の山場**: 50〜150 行 / 2 週間予算
  - 補助補題: `klDiv_prod_eq_klDiv` (`Measure.prod = · ⊗ₘ Kernel.const _ ·` 経由で `klDiv_compProd_left` から導く) を最初に書くと後続が楽になる
- **Phase 4-α 着手 ready**

---

## Phase 4-α: mutualInfo + 基本性質 + DPI

### スコープ

```lean
namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [MeasurableSpace X]
variable {Y : Type*} [MeasurableSpace Y]

/-- Mutual information via KL divergence.
`I(X; Y) := KL(P_{X,Y} ‖ P_X ⊗ P_Y)` -/
noncomputable def mutualInfo
    (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞ :=
  klDiv (μ.map (fun ω => (Xs ω, Yo ω)))
        ((μ.map Xs).prod (μ.map Yo))

theorem mutualInfo_nonneg (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) :
    0 ≤ mutualInfo μ Xs Yo := by
  -- klDiv は ℝ≥0∞ 値なので自明 (signature の都合)

theorem mutualInfo_eq_zero_iff_indep
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    mutualInfo μ Xs Yo = 0 ↔ IndepFun Xs Yo μ

theorem mutualInfo_comm
    (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) :
    mutualInfo μ Xs Yo = mutualInfo μ Yo Xs

/-- Data processing inequality: post-processing decreases mutual information.
Markov chain `X → Y → Z` (i.e. `Z = f(Y)` か Z は Y にのみ依存) で
`I(X; Z) ≤ I(X; Y)`. -/
theorem mutualInfo_le_of_postprocess
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) {Z : Type*} [MeasurableSpace Z]
    (f : Y → Z) (hf : Measurable f) :
    mutualInfo μ Xs (f ∘ Yo) ≤ mutualInfo μ Xs Yo

end InformationTheory.Shannon
```

### 鍵となる作業

> M0 で各補題の Mathlib 既存状況を確認済み (詳細は [`shannon-mathlib-inventory.md`](shannon-mathlib-inventory.md))。

0. **補助補題: `klDiv_prod_eq_klDiv`** — `klDiv (μ.prod ν₁) (μ.prod ν₂) = klDiv ν₁ ν₂` を `Measure.prod = · ⊗ₘ Kernel.const _ ·` 経由で `klDiv_compProd_left` から導く。10〜20 行。後続全部の起点
1. **`mutualInfo` の定義** (10 分)
2. **`mutualInfo_nonneg`** — `zero_le _` で 1 行 (klDiv が `ℝ≥0∞` 値)。`toReal` 版で書く場合は `klDiv_nonneg` (要確認) から
3. **`mutualInfo_comm`** — `Measure.prod_swap` ((μ.prod ν).map Prod.swap = ν.prod μ) + KL の `Measure.map Prod.swap` 不変性 (これも自作の可能性あり)。10〜20 行
4. **`mutualInfo_eq_zero_iff_indep`** — `indepFun_iff_map_prod_eq_prod_map_map` (`Probability/Independence/Basic.lean:701`) と `klDiv_eq_zero_iff` (`KullbackLeibler/Basic.lean:377`) を合成。5〜10 行
5. **DPI が Phase 4-α の山場** — 直接補題は Mathlib に**完全不在**。戦略: `f : Y → Z` を `Kernel.deterministic f` で kernel 化し、`compProd_map_condDistrib` で `μ.map (Xs, Yo)` を `(μ.map Xs) ⊗ₘ condDistrib Yo Xs μ` に disintegrate、`klDiv_compProd_eq_add` で chain rule を 2 回適用して比較。**50〜150 行 / 2 週間予算**
6. **stochastic kernel 版 DPI** (オプション) — `Z = κ(Y)` で `κ` が Markov kernel の場合への一般化。Phase 4-γ で必要なら追加

### ファイル構成

```
Common2026/Shannon/
  MutualInfo.lean   ← 定義 + 性質群
  DPI.lean          ← post-processing 不等式 (deterministic と stochastic の 2 形)
```

### Done 条件

- 上記 4 定理 (定義 + 3 性質 + DPI) が `lake env lean` で silent
- proof-log + metrics 取得済み
- `Common2026.lean` に `import Common2026.Shannon.MutualInfo` / `Common2026.Shannon.DPI` 追記

### 工数感

1〜2 週間。Phase 3 と同程度の plumbing を見込む。最大リスクは「`klDiv_compProd` の signature が DPI を素直に出せる形か」(Phase 4-M0 で事前確認)。

---

## Phase 4-β: Phase 3 condEntropy との bridge

### スコープ

X が `Fintype` のとき、Phase 4-α の `mutualInfo` (KL 形) と Phase 3 の `condEntropy` (Σ negMulLog 形) が `H(X) - H(X|Y)` で結ばれることを示す。

```lean
namespace InformationTheory.Shannon

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [Fintype X] [DecidableEq X]
  [MeasurableSpace X] [MeasurableSingletonClass X]
variable {Y : Type*} [MeasurableSpace Y]

/-- Shannon entropy of a discrete random variable. -/
noncomputable def entropy (μ : Measure Ω) (Xs : Ω → X) : ℝ :=
  ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})

/-- The MI/condEntropy bridge: for finite-alphabet X,
`I(X; Y) = H(X) - H(X | Y)`. -/
theorem mutualInfo_eq_entropy_sub_condEntropy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    (mutualInfo μ Xs Yo).toReal
      = entropy μ Xs - InformationTheory.MeasureFano.condEntropy μ Xs Yo

end InformationTheory.Shannon
```

### 鍵となる作業

1. **離散側で KL を展開する補題** — X Fintype なら `μ.map Xs` は離散測度、`μ.map (Xs, Yo)` は X 上の有限和 + Y 上の積分の混合。`PMF.integral_eq_sum` 系を経由
2. **`klDiv (P_{XY} ‖ P_X ⊗ P_Y)` を `∑_x ∫_y` に展開**し、`P_{XY}/(P_X · P_Y)` の log を `log P(x|y) - log P(x)` に分解
3. 期待値の線形性で `H(X) - H(X|Y)` の形に整理
4. **ENNReal ↔ Real の変換** — KL は `ℝ≥0∞`、condEntropy は `ℝ`。`toReal` を一貫して使い、`klDiv_lt_top` の証明 (P_{XY} ≪ P_X ⊗ P_Y は X Fintype + 確率測度から従う) が要る

### Done 条件

- bridge lemma が `lake env lean` で silent
- Phase 3 の `condEntropy` が Phase 4-α の `mutualInfo` で表現可能なことが明示される
- proof-log + metrics 取得済み

### 工数感

3〜5 日。新しい数学はなく純 plumbing だが、ENNReal ↔ Real の往復と離散和 ↔ 測度積分の橋渡しで時間が溶ける可能性がある。Phase 3 の `pointwise_fano` で `diracPMF` を経由した経験がそのまま流用できる見込み。

---

## Phase 4-γ: single-shot Shannon converse 🎯 **達成 (2026-05-10)**

### スコープ

Fano (Phase 3) + DPI (Phase 4-α) + bridge (Phase 4-β) を組み合わせて Shannon converse を導く。

**当初想定 (encoder 付き)**:

```lean
namespace InformationTheory.Shannon

theorem shannon_converse_single_shot
    {M X Y : Type*} [Fintype M] [Fintype X] [DecidableEq M] [Nonempty M]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y]
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → X) (Yo : Ω → Y) (decoder : Y → M)
    (hMsg : Measurable Msg) (hYo : Measurable Yo)
    (hencoder : Measurable encoder) (hdecoder : Measurable decoder)
    (hMsg_uniform : μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M) :
    Real.log (Fintype.card M) ≤
      (mutualInfo μ (encoder ∘ Msg) Yo).toReal +
        Real.binEntropy (errorProb μ Msg (decoder ∘ Yo)) +
        errorProb μ Msg (decoder ∘ Yo) * Real.log ((Fintype.card M : ℝ) - 1)

end InformationTheory.Shannon
```

> ⚠️ **encoder 版は実装で落とした** (Phase 4-γ 結果参照)。実装は `I(Msg; Yo)` 直接版。encoder 版は injective encoder の系として、または `Msg → encoder ∘ Msg → Yo` Markov 仮定の下で別補題として後付け可能 (Phase 5 候補)。

### 証明骨格 (純 plumbing)

```
log|M| = H(Msg)                                                  -- uniform message + Phase 4-β entropy
       = I(Msg; decoder ∘ Yo) + condEntropy(Msg | decoder ∘ Yo)  -- Phase 4-β bridge
       ≤ I(Msg; Yo) + condEntropy(Msg | decoder ∘ Yo)            -- Phase 4-α DPI (decoder)
       ≤ I(Msg; Yo) + h(Pe) + Pe · log(|M|-1)                    -- Phase 3 Fano (Measure.lean)
```

(encoder の DPI 1 段は実装では削除 — §結果参照。)

最後の Fano 適用には Phase 3 の `fano_inequality_measure_theoretic` をそのまま使える (X = M, decoder = id の系)。

### 鍵となる作業

1. **uniform message のエントロピー** — `H(Msg) = log |M|`。`hMsg_uniform` から計算。20 行程度
2. **decoder の DPI 適用** — Phase 4-α の DPI を 1 回呼ぶ。シンプル
3. **Phase 3 Fano の適用** — `fano_inequality_measure_theoretic` の signature と整合させる。`X` 引数を `M` (`Fintype` + `MeasurableSingletonClass`) として使う
4. **chain (`calc` / `linarith` で連結)** — 上の 3 行をそのまま Lean に書き下す

### Done 条件

- ✅ `Common2026/Shannon/Converse.lean` が `lake env lean` で silent (124 行 / 0 errors / 0 sorry)
- ✅ Phase 3 / 4-α / 4-β がすべて activated (主定理が `MeasureFano.fano_inequality_measure_theoretic`, `Shannon.mutualInfo_le_of_postprocess`, `Shannon.mutualInfo_eq_entropy_sub_condEntropy` を直接呼ぶ)
- ✅ proof-log + metrics 取得済み ([proof-log-shannon-converse.md](proof-log-shannon-converse.md), [metrics/shannon-converse.metrics.md](metrics/shannon-converse.metrics.md))
- 🟡 全体ふりかえり: 行数ベースの Fano vs Shannon plumbing 比較は下表に記録。session metrics は Fano Phase 1/2 と Shannon converse のみ取得済 (Phase 3 / 4-α / 4-β は未取得)、累計工数の定量比較は不揃い

### 工数感

1 週間予算。**実績: 1 セッション (14m 27s, 46 ツールコール, 3 失敗)** — ほぼ skeleton 1 ターン + 中身 1 ターンで完走。Phase 4-α / 4-β の積み上げで「組み合わせるだけ」になった効果。

### 撤退ライン

非該当。skeleton 着手前の plan 修正 (encoder 引数落とし、§結果参照) で polish 1 回入っただけで、本体の証明戦略は計画通り通った。

### Phase 4-γ 結果 (2026-05-10)

**実装と計画の差分: encoder を引数から落とした**。計画の `I(encoder ∘ Msg; Yo)` 版は Phase 4-α DPI (`mutualInfo_le_of_postprocess`) の方向と整合しない (DPI は postprocess 方向 `I(Xs; f∘Yo) ≤ I(Xs; Yo)` のみで、encoder 側 `I(Msg; Yo) ≤ I(encoder ∘ Msg; Yo)` は Markov 仮定 `Msg → encoder ∘ Msg → Yo` 別途要)。`I(Msg; Yo)` 直接版に切り替え、encoder 版は **Phase 5 候補**として deferred:

- (a) **injective encoder の系**: `encoder` injective なら `mutualInfo μ Msg Yo = mutualInfo μ (encoder ∘ Msg) Yo` が成立、これを bridge して encoder 付き版を導出
- (b) **Markov 仮定込み版**: `Msg → encoder ∘ Msg → Yo` を `condDistrib` レベルで定式化し、別補題で `mutualInfo μ Msg Yo ≤ mutualInfo μ (encoder ∘ Msg) Yo` を証明、本定理に bridge
- 100〜200 行追加見込み。ムーンショット成立 (sorry ゼロで通る) を遅らせないため見送り

**Fano vs Shannon plumbing 主役比較** (proof-log §1 を再掲)。「KL chain rule 主軸 plumbing は binEntropy 凹性主軸より速かったか」のデモ素材:

| Phase | 主要ファイル | 行数 | 新規補題の中核 | 性格 |
|---|---|---|---|---|
| Phase 3 (Fano Measure) | `Common2026/Fano/Measure.lean` | 数百行 | `fano_inequality_measure_theoretic` | 測度論経由の重実装 |
| Phase 4-α (DPI) | `Common2026/Shannon/DPI.lean` | 168 行 | `mutualInfo_le_of_postprocess` | klDiv の DPI 接続 |
| Phase 4-β (bridge) | `Common2026/Shannon/Bridge.lean` | 588 行 | `mutualInfo_eq_entropy_sub_condEntropy` | KL ↔ entropy − condEntropy 同値 |
| **Phase 4-γ (converse)** | `Common2026/Shannon/Converse.lean` | **124 行** | (組み合わせのみ) | **plumbing** |

Phase 4-α 〜 4-γ で計 880 行。Fano Phase 3 の `Measure.lean` 単体と同オーダー。Phase 4-β (bridge) が ENNReal ↔ Real / 離散和 ↔ 測度積分の往復で最も重く、γ は β が片付いた後の純組み合わせとして 1 セッションで完走。

**成果物**:

- `Common2026/Shannon/Converse.lean` (124 行、主定理 + private helper `entropy_of_uniform_msg`)
- `Common2026.lean` に `import Common2026.Shannon.Converse` 追記
- [`docs/proof-log-shannon-converse.md`](proof-log-shannon-converse.md) — 質的観察 (encoder 落とし判断、`.olean` 鮮度ハマり、PATH ハマり、`omit [Inst] in` パターン)
- [`docs/metrics/shannon-converse.{metrics,manifest}.{json,md}`](metrics/shannon-converse.metrics.md)

**ツール開発への示唆** (proof-log §6 を要約):
- 高: **inequality 方向の静的検証** — 計画 Lean 命題と利用予定補題の戻り方向を照合 (今回 encoder 落とし判断の自動化)
- 高: **`.olean` 鮮度診断** — `lake env lean` 失敗前の上流再ビルド提示 (recurring 問題)

---

## デモ / 対外発信の組み立て

各 Phase 完了時に、Fano と同様の 3 点セット:

1. **Lean ソース** — 証明本体
2. **proof-log** — 質的記録 (Mathlib KL API の探索、ENNReal/Real 往復のハマり所、欲しかったツール)
3. **metrics** — `scripts/session_metrics.ts` から取った定量データ

最終的に書きたい記事のラフ:

> 「**情報理論を専攻したことのない人間が、Claude Code と組んで、
> Mathlib の `klDiv` から Shannon converse まで N 日で形式化した記録**」
>
> - Fano プロジェクト (Phase 0〜3): 既存記録
> - Phase 4-M0 (Mathlib KL インベントリ): N 分
> - Phase 4-α (mutualInfo + DPI): N 時間
> - Phase 4-β (Phase 3 bridge): N' 時間
> - Phase 4-γ (single-shot converse): N'' 時間
> - Fano と Shannon の plumbing 主役の違い (`binEntropy` 凹性 vs `klDiv_compProd`) はどちらが軽かったか
> - Mathlib の情報理論 namespace の現状 (KL + Hamming + 符号理論はあるが Shannon 系は無い) と、Phase 4 で埋めた範囲

---

## 当面の next step

1. ~~このファイルをレビュー → 認識合わせ~~ (済)
2. **Fano Phase 3 の proof-log + metrics 取得** (Phase 4 開始前にやっておくと比較が綺麗)
3. ~~**Phase 4-M0 着手** — Mathlib KL API インベントリ調査、subagent 並列で 1 ターン~~ (済, 2026-05-09)
4. ~~Phase 4-M0 結果を見て、必要なら本計画書の Approach / Phase 4-α 節を更新~~ (済)
5. **Phase 4-α の skeleton 作成** — `Common2026/Shannon/MutualInfo.lean` の sorry-driven 出だし ([`shannon-mathlib-inventory.md`](shannon-mathlib-inventory.md) 末尾の skeleton をそのまま採用) ← **次これ**
6. **`klDiv_prod_eq_klDiv` 補助補題から sorry を割り始める**

---

## 失敗判定 / 撤退ライン

- **Phase 4-M0 で `klDiv` の DPI / monotonicity 補題が驚くほど未整備**だった場合
  → Phase 4-α の DPI を「Mathlib の不在を埋める PR ターゲット」として上流還元方向に倒す。Lean 側の Phase 4 スコープは「mutualInfo 整備 + Phase 3 bridge」までに縮める
- **Phase 4-α で 2 週間溶けて DPI が書けない**場合
  → mutualInfo 定義 + 基本性質だけで Phase 4-α を打ち止め、DPI は将来課題に。Phase 4-β / γ には到達せず Phase 4 全体を「mutualInfo 整備フェーズ」として publish。Fano プロジェクトの Phase 3.5 (randomized decoder) と並んで「やり残し」リストに入る
- **Phase 4-β の bridge で「ENNReal ↔ Real」の往復が想定外に重い**場合
  → bridge を `toReal` 限定で書き、ENNReal の世界では別途 Phase 4-β-bis として整備
- **Phase 4-γ で Markov chain の formulation が複雑すぎて 1 週間以上溶ける**場合
  → encoder / decoder を deterministic 関数に固定した最も簡単な形だけで converse を書き、確率的 encoder/decoder への一般化は Phase 5 に切り出す
- どのケースも proof-log に**正直に**記録する。Mathlib の薄い箇所を可視化したという結果自体がデモのデータポイント
