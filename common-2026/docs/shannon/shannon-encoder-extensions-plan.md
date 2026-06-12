# Shannon converse encoder 版補完計画 (Phase 4-δ)

**Status**: CLOSED ✅ — done (Ch.7 channel capacity; encoder-version converse extensions landed — Markov-chain encoder converse `shannon_converse_single_shot_markov_encoder` + `CondMutualInfo.lean` machinery, 0 sorry). NOTE: this is the encoder-extension completion plan, NOT the separate "strong converse asymptotic (Pe → 1, R > C)" future-work tracked in `textbook-roadmap.md`.

> **Parent**: [`shannon-moonshot-plan.md`](shannon-moonshot-plan.md) Phase 4-γ 結果セクションで deferred とした「encoder 付き版」を 2 形式で完成させるサブ計画。
> **Status (2026-05-10)**: Phase 4-δ-(a) **完了** (commit d4bec7c)。Phase 4-δ-(b) は inventory 完了 (`docs/shannon/shannon-condmi-inventory.md`)、skeleton 着手前。

> 実態整合 (2026-05-20): 両 Phase とも DONE-HONEST-HYPS (plan の (b) 「skeleton 着手前」記述は stale)。(a) `shannon_converse_single_shot_injective_encoder` (`InformationTheory/Shannon/Converse.lean:141`、`hencoder_inj : Function.Injective encoder` 仮定) と (b) `shannon_converse_single_shot_markov_encoder` (`:207`、`hmarkov : IsMarkovChain μ Msg (encoder ∘ Msg) Yo` 仮定) がいずれも 0 sorry で publish 済 (`CondMutualInfo.lean` も存在)。仮定は genuine analytic (injectivity / Markov chain)、pass-through 不在。

## Context

Phase 4-γ で `shannon_converse_single_shot` を `I(Msg; Yo)` 直接版で完成させたが、計画書当初の `I(encoder ∘ Msg; Yo)` 版は Phase 4-α DPI の方向と整合しないため落とした (`docs/proof-logs/proof-log-shannon-converse.md` §2 / §4.1)。本計画はその差分を 2 段で埋める:

- **Phase 4-δ-(a)**: `encoder` が injective な場合に系として `I(Msg; Yo) ≤ I(encoder ∘ Msg; Yo)` を出す (Phase 4-α DPI を 1 回追加で呼ぶだけ)
- **Phase 4-δ-(b)**: Markov 仮定 `Msg → encoder ∘ Msg → Yo` の下で同じ不等式を出す (条件付き mutualInfo + chain rule + 条件付き独立を新設)

(a) は encoder 版の **教科書的に最も自然な系** として、(b) は **Cover & Thomas 8.6 のあのチェーン**として、それぞれデモ価値が分かれる。(a) は記事素材の「encoder 版も書ける」一文用、(b) は次ムーンショット (ブロック符号 / 漸近) の Markov 整備の前段として効く。

## Approach

**(a) → (b) の順で 2 段。新規ファイルは (b) でだけ作る。**

```
(a) Converse.lean に系を 1 本追加 (~40 行)        ← まず軽い、Phase 4-α DPI 流用
       ─────────────────────────────────────
(b) CondMutualInfo.lean を新設 (~150-200 行)      ← Phase 4-α 級、条件付き MI を整備
    + Converse.lean に encoder Markov 版を追加 (~30 行)
```

### Approach の根幹

- **(a) は Phase 4-α DPI の対称化 1 回**で出る。新規補題ゼロ、`mutualInfo_comm` + `mutualInfo_le_of_postprocess` + `Function.Injective.hasLeftInverse` の合成で済む。「encoder injective ⇒ 左逆 `decoder'` が存在 ⇒ `Msg = decoder' ∘ (encoder ∘ Msg)` ⇒ DPI で `I(Yo; Msg) ≤ I(Yo; encoder ∘ Msg)` ⇒ 対称化」
- **(b) は条件付き MI を新規導入**する Phase 4-α 級の作業。Markov 仮定を `condIndepFun Msg Yo (encoder ∘ Msg) μ` または `condDistrib` 形で書き、chain rule `I(Msg, encoder∘Msg; Yo) = I(encoder∘Msg; Yo) + I(Msg; Yo | encoder∘Msg)` と「条件付き独立 ⇒ 条件付き MI = 0」を組んで結ぶ
- **(b) の最大リスク**は条件付き MI の Mathlib 在庫が薄い場合。Phase 4-α と同じく `klDiv` + `condDistrib` から自作する方針。Phase 4-M0 に類する事前 inventory を 1 ターンで挟むかどうかは (a) 完了時点で判断

---

## Phase 4-δ-(a): injective encoder の系

### スコープ

```lean
namespace InformationTheory.Shannon

theorem shannon_converse_single_shot_injective_encoder
    {M X Y : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y]
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → X) (Yo : Ω → Y) (decoder : Y → M)
    (hMsg : Measurable Msg) (hYo : Measurable Yo)
    (hencoder : Measurable encoder) (hdecoder : Measurable decoder)
    (hencoder_inj : Function.Injective encoder)
    (hMsg_uniform : μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M)
    (hMI_finite : mutualInfo μ (encoder ∘ Msg) Yo ≠ ∞) :
    Real.log (Fintype.card M) ≤
      (mutualInfo μ (encoder ∘ Msg) Yo).toReal +
        Real.binEntropy
          (InformationTheory.MeasureFano.errorProb μ Msg Yo decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg Yo decoder *
          Real.log ((Fintype.card M : ℝ) - 1)

end InformationTheory.Shannon
```

### 証明戦略

```
I(Msg; Yo) = I(Yo; Msg)                              -- mutualInfo_comm
           = I(Yo; decoder' ∘ (encoder ∘ Msg))       -- decoder' ∘ encoder = id (injective + Fintype)
           ≤ I(Yo; encoder ∘ Msg)                    -- Phase 4-α DPI (postprocess decoder')
           = I(encoder ∘ Msg; Yo)                    -- mutualInfo_comm
```

これを `shannon_converse_single_shot` の bound と組み合わせて `log|M| ≤ I(encoder ∘ Msg; Yo) + h(Pe) + Pe·log(|M|-1)` を出す。

### 鍵となる作業

1. **`decoder'` の構成** — `Function.Injective.hasLeftInverse` (Mathlib、古典論理) または `Fintype.bijInv` 系で `decoder' ∘ encoder = id`。`M` `Fintype` + `Nonempty` + `encoder` injective が要前提
2. **`decoder'` の measurability** — `M`, `X` Fintype + `MeasurableSingletonClass` なら全関数 measurable (`Measurable.of_discrete` 系)
3. **MI の対称化チェーン** — `mutualInfo_comm` を 2 回 + Phase 4-α DPI 1 回。`hMI_finite` を `mutualInfo μ (encoder ∘ Msg) Yo ≠ ∞` 側に移すために `mutualInfo_comm` 経由
4. **`shannon_converse_single_shot` への bridge** — 既存定理の bound に `I(Msg; Yo).toReal ≤ I(encoder ∘ Msg; Yo).toReal` を `linarith` で挟む

### Done 条件

- `InformationTheory/Shannon/Converse.lean` 末尾に `shannon_converse_single_shot_injective_encoder` を追加 (~40 行)
- `lake env lean InformationTheory/Shannon/Converse.lean` silent
- 既存 `shannon_converse_single_shot` を改変しない (純拡張)

### 工数感

**0.5〜1 セッション (30〜60 分)**。新規補題ゼロ、既存定理の合成のみ。最大の不確実性は `decoder'` measurability の補題探索 (`MeasurableSingletonClass` 経由の自動 measurability が `simp` で出るか、`Fintype` 経由で陽に書く必要があるか)。

---

## Phase 4-δ-(b): Markov 仮定込み版

### スコープ

```lean
namespace InformationTheory.Shannon

/-- 条件付き mutualInfo. -/
noncomputable def condMutualInfo
    (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) (Zs : Ω → Z) : ℝ≥0∞ :=
  -- 候補定式: Σ_z P(Z=z) · I(X;Y | Z=z) を kernel 経由で書く
  -- もしくは KL(P_{X,Y,Z} ‖ P_{X|Z} ⊗ P_{Y|Z} ⊗ P_Z) — 要検討
  sorry

/-- Markov chain `Xs → Zs → Yo` の条件付き独立性. -/
def IsMarkovChain (μ : Measure Ω) (Xs : Ω → X) (Zs : Ω → Z) (Yo : Ω → Y) : Prop :=
  -- condIndepFun Xs Yo (σ-algebra generated by Zs) μ
  -- もしくは condDistrib Yo (Xs, Zs) μ = condDistrib Yo Zs μ ∘ snd
  sorry

theorem mutualInfo_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Zs : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZs : Measurable Zs) (hYo : Measurable Yo) :
    mutualInfo μ (fun ω => (Xs ω, Zs ω)) Yo
      = mutualInfo μ Zs Yo + condMutualInfo μ Xs Yo Zs

theorem condMutualInfo_eq_zero_of_markov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Zs : Ω → Z) (Yo : Ω → Y) (...) :
    IsMarkovChain μ Xs Zs Yo →
    condMutualInfo μ Xs Yo Zs = 0

theorem mutualInfo_le_of_markov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Zs : Ω → Z) (Yo : Ω → Y) (...) :
    IsMarkovChain μ Xs Zs Yo →
    mutualInfo μ Xs Yo ≤ mutualInfo μ Zs Yo

end InformationTheory.Shannon
```

主応用 (Converse.lean):

```lean
theorem shannon_converse_single_shot_markov_encoder
    (...)
    (hMarkov : IsMarkovChain μ Msg (encoder ∘ Msg) Yo) :
    Real.log (Fintype.card M) ≤
      (mutualInfo μ (encoder ∘ Msg) Yo).toReal + h(Pe) + Pe · log(|M|-1)
```

### 証明戦略

```
I(Msg; Yo) ≤ I(Msg, encoder∘Msg; Yo)                 -- DPI (postprocess Prod.fst)
            = I(encoder∘Msg; Yo) + I(Msg; Yo | encoder∘Msg)   -- chain rule
            = I(encoder∘Msg; Yo) + 0                  -- Markov ⇒ condMI = 0
            = I(encoder∘Msg; Yo)
```

これを `shannon_converse_single_shot` に bridge する。

### 鍵となる作業

1. **条件付き mutualInfo の定式化** — Mathlib 在庫を 1 ターンで inventory (subagent 並列、Phase 4-M0 と同型)。期待される素材: `klDiv` + `condDistrib` + `Kernel.compProd`。新規が必要なら自前定義
2. **`IsMarkovChain` の定式化** — `ProbabilityTheory.condIndepFun` ([Probability/Independence/Conditional.lean] あれば) 流用、なければ `condDistrib` 等式形で自前
3. **chain rule** — `klDiv` の chain rule (`klDiv_compProd_eq_add`) を MI 形に下ろす。Phase 4-α `klDiv_prod_eq_klDiv` の延長
4. **条件付き独立 ⇒ 条件付き MI = 0** — `klDiv_eq_zero_iff` の条件付き版
5. **DPI for `Prod.fst`** — Phase 4-α DPI を `f := Prod.fst : M × X → M` で適用、`I(Msg, encoder∘Msg; Yo) ≥ I(Msg; Yo)`。`mutualInfo_comm` 経由
6. **converse 主応用** — 上記 chain と `shannon_converse_single_shot` の合成 (~30 行)

### ファイル構成

```
InformationTheory/Shannon/
  CondMutualInfo.lean   ← 新設、本フェーズの主役 (定義 + chain rule + Markov 系)
  Converse.lean         ← shannon_converse_single_shot_markov_encoder を末尾に追加
```

`InformationTheory.lean` に `import InformationTheory.Shannon.CondMutualInfo` を追記 (Converse の前)。

### Done 条件

- `CondMutualInfo.lean` の上記 4 定理 (定義 + chain rule + Markov 系 2 つ) が `lake env lean` silent
- `Converse.lean` の `shannon_converse_single_shot_markov_encoder` が silent
- proof-log + metrics 取得 (Phase 4-δ 全体まとめ、(a) と (b) を 1 ファイルに)

### 工数感

**1〜2 週間 / 100〜200 行**。Phase 4-α DPI と同オーダーの新規 plumbing。最大リスクは「条件付き独立の Mathlib API が `condDistrib` 経由で素直に書けるか」。Mathlib に `condIndepFun` の `condDistrib` 形変換補題が無ければ自作 100 行追加もありうる。

---

## ファイル構成 (Phase 4-δ 終了時)

```
InformationTheory/Shannon/
  MutualInfo.lean         ← Phase 4-α、不変
  DPI.lean                ← Phase 4-α、不変
  Bridge.lean             ← Phase 4-β、不変
  Converse.lean           ← Phase 4-γ + δ-(a) + δ-(b)、3 定理が並ぶ
  CondMutualInfo.lean     ← Phase 4-δ-(b) 新設
```

`shannon_converse_single_shot` (γ) / `_injective_encoder` (δ-a) / `_markov_encoder` (δ-b) の 3 形が同じファイルに揃い、教科書 Cover & Thomas 8.9 の formulation を 3 視点でカバー。

---

## 撤退ライン

- **(a) の `decoder'` measurability で詰まる**場合 → `Fintype` + `MeasurableSingletonClass` だけでは足りないと判明したら、`encoder` を `MeasurableEquiv` (image への restrict) で書き直す形に switch。30 行追加見込み
- **(b) の条件付き MI inventory で「Mathlib に `condIndepFun` 系が殆ど無い」場合** → (b) を打ち止め、(a) だけで Phase 4-δ closed。「Markov 版は Mathlib `condIndepFun` 整備の前段が要る」という事実自体をデモのデータポイントにする
- **(b) の chain rule 証明が 1 週間で書けない**場合 → 条件付き MI 定義 + 性質群 (nonneg, comm) だけで Phase 4-δ-(b) を打ち止め、Markov 版 converse は将来課題に。proof-log で「Mathlib の薄さの可視化」として記録

---

## 当面の next step

1. ~~**Phase 4-δ-(a) の skeleton 作成**~~ ✅ commit d4bec7c (2026-05-10)
2. ~~**`decoder'` の構成と measurability**~~ ✅ `Function.invFun` + `Function.leftInverse_invFun` + `measurable_of_countable` で 1 行ずつ
3. ~~**(a) の sorry を埋めて silent**~~ ✅ 一発で silent (~30 行)
4. ~~**Phase 4-δ-(b) の inventory**~~ ✅ `docs/shannon/shannon-condmi-inventory.md` に subagent 3 並列の結果を統合 (2026-05-10)
5. **Phase 4-δ-(b) skeleton 作成** ← **次これ**
   - `InformationTheory/Shannon/CondMutualInfo.lean` 新設
   - `condMutualInfo` 定義 + `IsMarkovChain` 定義 (β 形式 = condDistrib 等式形) + chain rule + Markov 系 2 つ + DPI for Prod.fst の skeleton (5 sorry)
   - inventory §着手順 #1〜#5 を順次充填
6. **(b) Converse.lean に主応用** — `shannon_converse_single_shot_markov_encoder` を末尾に追加
7. **proof-log + metrics** — Phase 4-δ-(a) と (b) を 1 ファイルにまとめて closure

---

## 参照

- 親計画: [`shannon-moonshot-plan.md`](shannon-moonshot-plan.md) — Phase 4-γ 結果セクションに deferred 経緯
- Phase 4-γ proof-log: [`proof-log-shannon-converse.md`](proof-logs/proof-log-shannon-converse.md) §2「設計判断: encoder を引数から落とした」
- Phase 4-α DPI: `InformationTheory/Shannon/DPI.lean:139` `mutualInfo_le_of_postprocess`
- Phase 4-α MI: `InformationTheory/Shannon/MutualInfo.lean:36` `mutualInfo` / `:93` `mutualInfo_comm`
- Phase 4-γ converse: `InformationTheory/Shannon/Converse.lean:80` `shannon_converse_single_shot`
