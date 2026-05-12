# 再利用テスト 2026-05 — Channel coding converse (n-variable, iid input)

`docs/reuse-test-plan.md` に基づく、既存 API の bridge-free 合成テスト。

ターゲット: **n 変数 i.i.d. 入力での channel coding converse (Markov encoder 版)**。

---

## §1 — ペーパー証明

### §1.1 ターゲット statement

設定:

- `Ω` 確率空間、`μ : Measure Ω` 確率測度。
- `M` メッセージ集合 (`Fintype`, `|M| ≥ 2`)。`Msg : Ω → M` 一様。
- `α, β` 有限アルファベット (`Fintype + MeasurableSingletonClass`)。
- `encoder : M → (Fin n → α)`、コードワード `X^n := encoder ∘ Msg`。
- `Ys : Fin n → Ω → β` 通信路出力、`Yo := fun ω i => Ys i ω : Ω → (Fin n → β)`。
- `decoder : (Fin n → β) → M`、誤り `Pe := μ {Msg ≠ decoder ∘ Yo}`。

仮定:

- (Markov) `IsMarkovChain μ Msg (encoder ∘ Msg) Yo` —— `Msg → X^n → Y^n`。
- (i.i.d.) 通信路の memoryless 化 + 入力分布の i.i.d. 化:
  - `μ.map (fun ω i => (X^n_i ω, Y^n_i ω)) = Measure.pi (i ↦ μ.map (i 番目))`、X 単独 / Y 単独でも同様。
  - `∀ i, μ.map (i 番目の同時) = μ.map (0 番目の同時)` (copy 仮定、X / Y 単独でも同様)。
- (有限) `mutualInfo μ (encoder ∘ Msg) Yo ≠ ∞`。

結論:

```
Real.log |M| ≤ n · I(X_0; Y_0).toReal
              + h(Pe) + Pe · log(|M| − 1)
```

ここで `I(X_0; Y_0) := mutualInfo μ (fun ω => X^n_0 ω) (Ys 0)`、左辺の `n` は係数 (高々 `n` 倍にスケールするのは MI 項のみで、Fano 項は無増)。

### §1.2 ペーパー証明

```
log|M| ≤ I(encoder ∘ Msg; Y^n).toReal + h(Pe) + Pe·log(|M|−1)   -- (A) shannon_converse_single_shot_markov_encoder
       = (n • I(X_0; Y_0)).toReal     + h(Pe) + Pe·log(|M|−1)   -- (B) mutualInfo_iid_eq_nsmul で書き換え
       = n · I(X_0; Y_0).toReal       + h(Pe) + Pe·log(|M|−1)   -- (C) ENNReal.toReal_nsmul (Mathlib 既存)
```

(A) は `Converse.lean:204` の Markov encoder 系単一ショット converse そのもの。
内部で:
  * Markov 仮定から `I(Msg; Y^n) ≤ I(encoder ∘ Msg; Y^n)` (`mutualInfo_le_of_markov`)、
  * `shannon_converse_single_shot` (Fano 含む) で結論。

(B) は `MIChainRule.lean:392` の i.i.d. corollary そのもの。
内部で `mutualInfo_pi_eq_sum` (product law ⇒ ∑) + copy 仮定で n 倍に collapse。

(C) は `ENNReal` で `(n • x).toReal = n * x.toReal`。Mathlib 一行。

### §1.3 4 API verbatim signature

#### `Shannon.shannon_converse_single_shot_markov_encoder`

`Common2026/Shannon/Converse.lean:207`

```lean
theorem shannon_converse_single_shot_markov_encoder
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → X) (Yo : Ω → Y) (decoder : Y → M)
    (hMsg : Measurable Msg) (hYo : Measurable Yo)
    (hencoder : Measurable encoder) (hdecoder : Measurable decoder)
    (hmarkov : IsMarkovChain μ Msg (encoder ∘ Msg) Yo)
    (hMsg_uniform :
      μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M)
    (hMI_finite : mutualInfo μ (encoder ∘ Msg) Yo ≠ ∞) :
    Real.log (Fintype.card M) ≤
      (mutualInfo μ (encoder ∘ Msg) Yo).toReal +
        Real.binEntropy
          (InformationTheory.MeasureFano.errorProb μ Msg Yo decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg Yo decoder *
          Real.log ((Fintype.card M : ℝ) - 1)
```

ターゲットでの呼び出し: `X := Fin n → α`, `Y := Fin n → β`, `Yo := (fun ω i => Ys i ω)`。
[Fintype α] [MeasurableSingletonClass α] + 同 β から `StandardBorelSpace (Fin n → α)`
および `StandardBorelSpace (Fin n → β)` は **derive 経路を確認する必要**:

* `Fintype α + MeasurableSingletonClass α ⇒ DiscreteMeasurableSpace α ⇒ StandardBorelSpace α` (Mathlib 既存)
* `Pi` への lift は `Pi.instStandardBorelSpace` または `Fin` の有限性で別経路。

→ Phase 2 で 1 行 `haveI` が要るか確認。**新規 lemma は不要**の見込み。

#### `Shannon.mutualInfo_iid_eq_nsmul`

`Common2026/Shannon/MIChainRule.lean:392`

```lean
theorem mutualInfo_iid_eq_nsmul
    {n : ℕ} (hn : 0 < n)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_iid_joint : μ.map (fun ω (i : Fin n) => (Xs i ω, Ys i ω))
                      = Measure.pi (fun i => μ.map (fun ω => (Xs i ω, Ys i ω))))
    (h_iid_X : μ.map (fun ω (i : Fin n) => Xs i ω)
                  = Measure.pi (fun i => μ.map (Xs i)))
    (h_iid_Y : μ.map (fun ω (i : Fin n) => Ys i ω)
                  = Measure.pi (fun i => μ.map (Ys i)))
    (h_copy : ∀ i, μ.map (fun ω => (Xs i ω, Ys i ω))
                      = μ.map (fun ω => (Xs ⟨0, hn⟩ ω, Ys ⟨0, hn⟩ ω)))
    (h_copy_X : ∀ i, μ.map (Xs i) = μ.map (Xs ⟨0, hn⟩))
    (h_copy_Y : ∀ i, μ.map (Ys i) = μ.map (Ys ⟨0, hn⟩)) :
    mutualInfo μ (fun ω i => Xs i ω) (fun ω i => Ys i ω)
      = n • mutualInfo μ (Xs ⟨0, hn⟩) (Ys ⟨0, hn⟩)
```

α, β 側に `[Fintype] [MeasurableSpace] [MeasurableSingletonClass] [Nonempty]` を要求 (section variable)。

呼び出し: `Xs i ω := encoder (Msg ω) i` で `fun ω i => Xs i ω = encoder ∘ Msg`。

#### `Shannon.mutualInfo_chain_rule_fin`

`Common2026/Shannon/MIChainRule.lean:117`

```lean
theorem mutualInfo_chain_rule_fin
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (Yo : Ω → Y) (hYo : Measurable Yo) :
    mutualInfo μ (fun ω i => Xs i ω) Yo
      = ∑ i : Fin n,
          condMutualInfo μ (Xs i) Yo
            (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
```

**本テストでは未使用**。i.i.d. 入力に対しては `mutualInfo_iid_eq_nsmul` がより直接的に
`n · I(X_0; Y_0)` を与えるため、chain rule 経由の `∑ I(X_i; Y_i | X^{<i})` 展開と
"memoryless channel ⇒ 各項 ≤ I(X_i; Y_i)" の追加ステップが不要となる。

非 i.i.d. 入力 (general DMC converse with average input distribution) への拡張時には
`mutualInfo_chain_rule_fin` が主役になる。本テストの scope 外。

#### `MeasureFano.fano_inequality_measure_theoretic`

`Common2026/Fano/Measure.lean:224`

```lean
theorem fano_inequality_measure_theoretic
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (decoder : Y → X)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hdec : Measurable decoder)
    (hcard : 2 ≤ Fintype.card X) :
    condEntropy μ Xs Yo ≤
      Real.binEntropy (errorProb μ Xs Yo decoder)
        + errorProb μ Xs Yo decoder * Real.log ((Fintype.card X : ℝ) - 1)
```

`shannon_converse_single_shot` の **内部で 1 回呼ばれる**ため、本テストでは
外向きには登場しない。`single_shot` のブラックボックス利用に閉じる。

### §1.4 必要な追加 facts (bridge ではない、Mathlib 直接)

| fact | 用途 |
|---|---|
| `ENNReal.toReal_nsmul` (or `nsmul_eq_mul` + `ENNReal.toReal_mul`) | `(n • I).toReal = n · I.toReal` |
| `StandardBorelSpace (Fin n → γ)` for finite γ | markov_encoder の type-class hypotheses |
| `Measurable encoder` for `encoder : M → (Fin n → α)` | M Fintype ⇒ `measurable_of_countable` で自動 |

いずれも Mathlib 既存。本ライブラリ側で新規補題を書く必要なし。

---

## §2 — Lean 化試行

`Common2026/Shannon/ChannelCodingConverse.lean` (新規、85 行) に `channel_coding_converse_iid`
1 本を定義。`lake env lean` 単独パス、`sorry` 残 0、Common2026.lean に import 追加済み。

### §2.1 証明本体 (要旨)

```lean
-- Step 0: auto-derive measurability + type-class hypotheses
have h_encoder : Measurable encoder := measurable_of_countable _
have h_X_full  : Measurable (fun ω => encoder (Msg ω)) := h_encoder.comp hMsg
have h_Yo      : Measurable (fun ω (i : Fin n) => Ys i ω) :=
  measurable_pi_iff.mpr hYs

-- Step 1: shannon_converse_single_shot_markov_encoder
have h_step1 :=
  shannon_converse_single_shot_markov_encoder (X := Fin n → α)
    μ Msg encoder (fun ω i => Ys i ω) decoder
    hMsg h_Yo h_encoder hdecoder hmarkov hMsg_uniform hcard hMI_finite

-- Step 2: mutualInfo_iid_eq_nsmul で I(X^n; Y^n) = n • I(X_0; Y_0)
set Xs : Fin n → Ω → α := fun i ω => encoder (Msg ω) i
have hXs_meas : ∀ i, Measurable (Xs i) := fun i =>
  (measurable_pi_apply i).comp h_X_full
have h_step2 :=
  mutualInfo_iid_eq_nsmul hn μ Xs Ys hXs_meas hYs
    h_iid_joint h_iid_X h_iid_Y h_copy h_copy_X h_copy_Y

-- Step 3: η-展開で (encoder ∘ Msg) ↔ (fun ω => encoder (Msg ω)) を揃え、
-- ENNReal.toReal_nsmul + nsmul_eq_mul で n • _ を n * _.toReal に。
have h_pi_eq_encoder :
    (fun ω (i : Fin n) => Xs i ω) = fun ω => encoder (Msg ω) := rfl
rw [h_pi_eq_encoder] at h_step2
rw [show (encoder ∘ Msg) = fun ω => encoder (Msg ω) from rfl,
    h_step2, ENNReal.toReal_nsmul, nsmul_eq_mul] at h_step1
exact h_step1
```

### §2.2 bridge 候補一覧

**(なし)** — 既存 API のみで n-channel converse まで到達。

### §2.3 観察された摩擦点 (非 bridge)

これらは **新規補題なし** で吸収できたが、構成時に整合させる必要があった箇所:

1. **η-展開ギャップ** `encoder ∘ Msg` (function composition) と `fun ω => encoder (Msg ω)`
   (η-expanded form)。defeq だが `rw` がパターン一致しないので `show ... from rfl` で
   明示的に書き換えた。
2. **`(n • I).toReal = n * I.toReal`** は `ENNReal.toReal_nsmul` + `nsmul_eq_mul` の
   2 段ステップ。Mathlib 既存だが 1 段で済む統合形 (`ENNReal.toReal_nsmul_mul` 等) は無い。
   bridge ではなく純粋な API 呼び順の問題。
3. **StandardBorelSpace (Fin n → α/β)** の type-class derivation: α, β が `Fintype +
   MeasurableSingletonClass` から `DiscreteMeasurableSpace + Countable` 経由で
   `StandardBorelSpace` が出る + `pi_countable` instance で Fin n → α まで自動。明示
   `haveI` 不要。
4. **`DecidableEq α/β` の linter warning**: section variable が unused なので
   `omit [DecidableEq α] [DecidableEq β] in` を docstring の前に付ける。

---

## §3 — 結論

**合格 (bridge 不要)**: 既存 4 API のうち実質 3 個 (`shannon_converse_single_shot_markov_encoder`、
`mutualInfo_iid_eq_nsmul`、内部の `fano_inequality_measure_theoretic`) の合成だけで
n-channel converse まで到達。新規補題ゼロ、`lake env lean` 単独パス、`sorry` 残 0。

### §3.1 観察 / 含意

- **`shannon_converse_single_shot_markov_encoder` の API 設計が n-channel スケーリング
  に対し**過剰仮定を要求していない**: encoder の型を generic `M → X` に保ち、X 側で
  `StandardBorelSpace` を要求するのが正解だった。X := Fin n → α は finite Fintype 経由で
  自動 standard Borel 化、特別な扱い不要。
- **`mutualInfo_iid_eq_nsmul` の hypotheses 6 本 (iid joint + 2 marginals + copy joint
  + 2 copies)** はすべてターゲットの hypotheses にそのまま流れ込んだ。bridge ゼロで API が
  matched するということは、設計時に "i.i.d. + memoryless channel" シナリオを想定していた
  証拠。
- **`mutualInfo_chain_rule_fin` は本テストでは未使用**。iid 入力の場合は `iid_eq_nsmul`
  が直接 `n • I(X_0; Y_0)` を返すため、chain rule 経由 + memoryless channel での
  per-summand bound (`I(X_i; Y_i | X^{<i}) ≤ I(X_i; Y_i)`) という追加ステップが回避できる。
  これは **非 i.i.d. 入力での DMC converse** (general statement: average input distribution)
  でしか chain rule の出番が無いことを示唆。本テスト範囲外の拡張テーマ。
- **🟡 "uniform input"** 仮定 (audit §4 で flag された 9 件のうち 1 つ) は n-channel
  スケーリングを妨げない: single-shot 段で uniform 仮定を消費し、iid 段は input 分布
  非依存に作用するため、scope は **per-symbol** で済む。
  - これは **分岐 B (statement 修復) で uniform 仮定を緩める必要性が低い**ことを意味する。
    uniform は textbook "log M = H(Msg)" を出すための都合のいい仮定であり、n-channel
    スケーリング自体は uniform 不要。修復の優先順位は他の 🟡 案件 (fixed p, average error
    等) の方が高いと判断。

### §3.2 次フェーズへの引き継ぎ

- 本テスト合格を踏まえ、moonshot seeds `D-1` (ChannelCoding 強形 / Converse) は
  **設計再検討のフェーズに進める** 段階に達している (n-channel API が揃った)。
- 残った 🟡 9 件のうち、`channel_coding_achievability` 系 (fixed p, average error の n
  変数化) の修復 / 拡張は別タスクとして起こす価値あり。本テスト同様 `IIDProductInput.lean`
  + `ChannelCodingAchievability.lean` の API 表面確認から始めるべき。

