# Shannon ムーンショット計画 🌙

> **Status (2026-05-09): 計画段階**。Fano ムーンショット ([fano-moonshot-plan.md](fano-moonshot-plan.md)) の Phase 3 達成を前提とする後継プロジェクト。
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

Fano Phase 3 では `binEntropy` 凹性 + Bochner Jensen を主役にした。Phase 4 では **`klDiv_compProd` 系の chain rule** を主役にする。

```
KL(μ ⊗ κ ‖ ν ⊗ ρ) = KL(μ ‖ ν) + ∫ KL(κ(x) ‖ ρ(x)) dμ
```

ここから次のものが構造的に出てくる:

- **DPI**: kernel `f` を片側にだけ適用して `KL(f_*μ ‖ f_*ν) ≤ KL(μ ‖ ν)`。MI に翻訳すると `I(X; f(Y)) ≤ I(X; Y)`
- **MI chain rule**: `I(X; Y, Z) = I(X; Y) + I(X; Z | Y)`
- **MI と独立性**: `I(X; Y) = 0 ↔ X ⫫ Y`

つまり「**klDiv chain rule から構造的に出てくるもの**」を順番に取り出すのが Phase 4 の基本動作。新規の凹性 Jensen は Phase 3 で組み終わっているので、Phase 4 では発生しないはず（と現時点では予想）。

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

1. **`mutualInfo` の定義** (10 分)
2. **`mutualInfo_nonneg`** — klDiv が `ℝ≥0∞` 値なので signature 上自明。`toReal` 版で書く場合は `klDiv_nonneg` から
3. **`mutualInfo_comm`** — `Measure.prod_swap` 系 + KL の swap 不変性
4. **`mutualInfo_eq_zero_iff_indep`** — KL=0 ↔ μ=ν の既存補題から
5. **DPI が Phase 4-α の山場** — Markov 構造 (`Z = f(Y)`) を「kernel の合成」で表現し、`klDiv_compProd` から導く。Phase 3 の `condDistrib` を使い回せる可能性が高い
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

## Phase 4-γ: single-shot Shannon converse

### スコープ

Fano (Phase 3) + DPI (Phase 4-α) + bridge (Phase 4-β) を組み合わせて Shannon converse を導く。

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

### 証明骨格 (純 plumbing)

```
log|M| = H(Msg)                                                  -- uniform message + Phase 4-β entropy
       = I(Msg; decoder ∘ Yo) + condEntropy(Msg | decoder ∘ Yo)  -- Phase 4-β bridge
       ≤ I(Msg; Yo) + condEntropy(Msg | decoder ∘ Yo)            -- Phase 4-α DPI (decoder)
       ≤ I(encoder ∘ Msg; Yo) + condEntropy(Msg | decoder ∘ Yo)  -- Phase 4-α DPI (encoder, 逆向き)
       ≤ I(encoder ∘ Msg; Yo) + h(Pe) + Pe · log(|M|-1)          -- Phase 3 Fano (Measure.lean)
```

最後の Fano 適用には Phase 3 の `fano_inequality_measure_theoretic` をそのまま使える (X = M, decoder の Markov 化が必要)。

### 鍵となる作業

1. **uniform message のエントロピー** — `H(Msg) = log |M|`。`hMsg_uniform` から計算。20 行程度
2. **encoder / decoder の DPI 適用** — Phase 4-α の DPI を 2 回呼ぶ。シンプル
3. **Phase 3 Fano の適用** — `fano_inequality_measure_theoretic` の signature と整合させる。`X` 引数を `M` (`Fintype` + `MeasurableSingletonClass`) として使う
4. **chain (`calc` で連結)** — 上の 4 行をそのまま Lean に書き下す

### Done 条件

- `Common2026/Shannon/Converse.lean` が `lake env lean` で silent
- Phase 3 / 4-α / 4-β がすべて activated されている (= 削除すると converse が壊れる)
- proof-log + metrics 取得済み
- 全体ふりかえり: Fano プロジェクト (Phase 0〜3) + Shannon プロジェクト (Phase 4-M0〜γ) の累計工数とツールコール数を比較した metrics サマリ

### 工数感

1 週間。証明本体は短いが、measurability assumption と Markov chain の formulation、`hMsg_uniform` の使い回しに時間がかかる見込み。

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

1. このファイルをレビュー → 認識合わせ
2. **Fano Phase 3 の proof-log + metrics 取得** (Phase 4 開始前にやっておくと比較が綺麗)
3. **Phase 4-M0 着手** — Mathlib KL API インベントリ調査、subagent 並列で 1 ターン
4. Phase 4-M0 結果を見て、必要なら本計画書の Approach / Phase 4-α 節を更新
5. **Phase 4-α の skeleton 作成** — `Common2026/Shannon/MutualInfo.lean` の sorry-driven 出だし

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
