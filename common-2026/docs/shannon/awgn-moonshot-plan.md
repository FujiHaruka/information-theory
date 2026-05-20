# AWGN Channel Capacity ムーンショット計画 🌙 (T2-A)

> 実態整合 (2026-05-20): DONE-HONEST-HYPS — headline `awgn_channel_coding_theorem`
> (`Common2026/Shannon/AWGNMain.lean:59`) は achievability (F-1 `IsAwgnTypicalityHypothesis`) +
> MI bridge (F-2) + converse (F-3 `IsAwgnConverseHypothesis`) を **honest pass-through hyp** で publish (`:= True` ではない、0 sorry)。
> `IsAwgnTypicalityHypothesis` (`AWGNAchievability.lean:39`)・`IsAwgnConverseHypothesis` (`AWGNConverse.lean:56`) は実体ある非自明 Prop。
> F-1 kernel measurability のみ `AWGNF1Discharge.lean:60` で完全 discharge 済。
> **注意**: `AWGNF2F3Discharge.lean` の `awgn_theorem_F1F2F3_discharged` (L294) は F-2/F-3 の*実 discharge ではない* —
> `IsAwgnF2DecodingHypothesis`/`IsAwgnF3ChainHypothesis` は元 hyp と同形の alias (id-like reduction)、
> `IsAwgnF3PerLetterHypothesis` (`AWGNF2F3Discharge.lean:229`) は `:= ... True` の placeholder。F-2/F-3 の実体は未着手。

<!--
雛形メモ (moonshot-plan-template.md より):
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 削除/廃止された Phase は ~~取り消し線~~ で残す（完全削除しない、過去参照のため）
- 判断ログは append-only。Phase 中の方針変更・撤退・当初仮定の修正を記録
-->

> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 2 — T2-A. AWGN Channel
> Capacity (Cover-Thomas Ch.9)」
>
> **Predecessor (inventory)**: [`awgn-mathlib-inventory.md`](awgn-mathlib-inventory.md)
> (643 行、Gaussian closed-form 100% / continuous entropy 100% / discrete channel coding
> 100% (型クラス壁あり) / AWGN 専用 layer 0% (要自作)、撤退ライン候補 3 本 + 危険箇所
> トップ 5、着手 skeleton 200 行)
>
> **Status (2026-05-19)**: 着手前。inventory 完了済、自作要素 6 件 (`awgnChannel` kernel +
> Markov instance / `AwgnCode` measurability+power-constraint bundle / `mutualInfo` closed
> form bridge / `awgnCapacity` 定義 + 等号 / continuous achievability / continuous converse)
> を確定。**3 ファイル分離戦略** (`AWGN.lean` / `AWGNAchievability.lean` / `AWGNConverse.lean`)
> 採用 (判断ログ #2 候補)。**撤退ライン F-1 + F-2 の組合せ発動を想定**して計画 (seed 規模
> 1000-1500 行に収めるため)。
>
> **Goal**: 新規 3 ファイル (`Common2026/Shannon/AWGN.lean` + `AWGNAchievability.lean` +
> `AWGNConverse.lean`) で **Cover-Thomas Theorem 9.1.1 + 9.1.2** (AWGN channel capacity
> `C = (1/2) log(1 + P/N)` の closed form + achievability + converse) を **`Tendsto` /
> sandwich 形 + hypothesis pass-through 形**で publish。
>
> **撤退ライン**: [F-1] continuous achievability の sphere packing / joint typicality を
> `h_typicality` hypothesis に外出し / [F-2] `mutualInfo` の `I = h(Y) - h(Y|X)` bridge を
> `h_mi_bridge` hypothesis に外出し / [F-3] converse per-letter max-entropy の `h_ent_int`
> を converse 全体の追加 hypothesis に外出し (詳細 §撤退ライン、inventory §F に対応)。

## 進捗

- [x] Phase 0 — Mathlib + Common2026 API 在庫 ✅ → [`awgn-mathlib-inventory.md`](awgn-mathlib-inventory.md)
- [x] Phase A — `awgnChannel` kernel + `AwgnCode` + `mutualInfo` closed-form bridge + `awgnCapacity` 定義 + 等号 ✅ (`AWGN.lean`, 275 行, F-2 + F-4 採用)
- [x] Phase B — Achievability (F-1 hypothesis pass-through 形) ✅ (`AWGNAchievability.lean`, 72 行)
- [x] Phase C — Converse (F-3 hypothesis pass-through 形) ✅ (`AWGNConverse.lean`, 94 行)
- [x] Phase D — 主定理 wrapper (`awgn_channel_coding_theorem`) ✅ (`AWGNMain.lean` 新規, 107 行) — 判断 #4 で `AWGN.lean` 末尾から `AWGNMain.lean` へ移動
- [x] Phase V — verify (4 ファイル `lake env lean` clean、0 sorry / 0 errors) ✅ (Common2026.lean 編入はオーケストレータが実施)

## ゴール / Approach

### Goal (最終定理 signature)

```lean
namespace InformationTheory.Shannon.AWGN

/-- **AWGN channel kernel**: 入力 `x : ℝ` に対し出力 `Y = x + Z` (`Z ∼ 𝒩(0, N)`)
の law `gaussianReal x N` を返す Markov kernel。 -/
noncomputable def awgnChannel (N : ℝ≥0) :
    InformationTheory.Shannon.ChannelCoding.Channel ℝ ℝ

instance awgnChannel.instIsMarkovKernel (N : ℝ≥0) : IsMarkovKernel (awgnChannel N)

/-- **AWGN code** — block length `n`, M codewords, output power constraint ≤ P, +
decoder measurability bundle (`Code ℝ ℝ` で抜けていた箇所、§危険 2)。 -/
structure AwgnCode (M n : ℕ) (P : ℝ) where
  encoder : Fin M → (Fin n → ℝ)
  decoder : (Fin n → ℝ) → Fin M
  decoder_meas : Measurable decoder
  power_constraint : ∀ m : Fin M, (∑ i : Fin n, (encoder m i)^2) ≤ (n : ℝ) * P

/-- Forget the bundle to get a bare `Code M n ℝ ℝ`. -/
noncomputable def AwgnCode.toCode {M n : ℕ} {P : ℝ} (c : AwgnCode M n P) :
    InformationTheory.Shannon.ChannelCoding.Code M n ℝ ℝ

/-- **Power-constrained AWGN capacity**: `sup_{p : E[X²] ≤ P} I(p; W_awgn)` の closed form。 -/
noncomputable def awgnCapacity (P : ℝ) (N : ℝ≥0) : ℝ :=
  sSup ((fun p : Measure ℝ =>
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (awgnChannel N)).toReal) ''
        { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P })

/-- **Closed form (Cover-Thomas 9.1)**: `C(P, N) = (1/2) log(1 + P/N)`. -/
theorem awgnCapacity_eq
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_mi_bridge : /- 撤退ライン F-2 hypothesis (§撤退ライン F-2) -/) :
    awgnCapacity P N = (1/2) * Real.log (1 + P / (N : ℝ))

/-- **Achievability (Cover-Thomas 9.1.1)** — F-1 hypothesis pass-through 形。 -/
theorem awgn_achievability
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_typicality : /- 撤退ライン F-1 hypothesis (§撤退ライン F-1) -/)
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
        ∀ m, (c.toCode.errorProbAt (awgnChannel N) m).toReal < ε

/-- **Converse (Cover-Thomas 9.1.2)** — F-3 hypothesis pass-through 形。 -/
theorem awgn_converse
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_per_letter_aux : /- 撤退ライン F-3 hypothesis (§撤退ライン F-3) -/)
    {M n : ℕ} (hM : 2 ≤ M) (c : AwgnCode M n P)
    (Pe : ℝ) (hPe : ...) :
    Real.log M
      ≤ (n : ℝ) * ((1/2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1)

/-- **AWGN main theorem (sandwich)** — achievability + converse + closed-form capacity。 -/
theorem awgn_channel_coding_theorem
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_typicality : /- F-1 -/) (h_mi_bridge : /- F-2 -/) (h_per_letter_aux : /- F-3 -/)
    {R : ℝ} (hR_pos : 0 < R) (hR_lt_C : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
        ∀ m, (c.toCode.errorProbAt (awgnChannel N) m).toReal < ε

end InformationTheory.Shannon.AWGN
```

statement 形 (`Tendsto` 直書き vs `DotEq` corollary、achievability / converse split の粒度、
3 撤退ラインの具体 hypothesis 形) は **Phase 0 着手時の判断 #1 で確定** (inventory §F の
hypothesis 形 reference + 既存 Cramér / Stein / Chernoff の流儀踏襲)。

### Approach (overall strategy / shape of solution)

**戦略の shape**: Cover-Thomas Ch.9 の AWGN 容量公式は **(a) Gaussian の精密計算 (closed-form
KL / convolution / entropy) + (b) discrete Shannon noisy channel coding の continuous 化** の
2 層で組む。Mathlib + Common2026 では:

```
[Gaussian closed-form layer]                  [Channel coding abstraction layer]

A.1 gaussianReal_conv_                  ◄─────  B.1 Channel α β := Kernel α β (既存)
    gaussianReal (既存)                          B.2 mutualInfoOfChannel (既存)
A.2 differentialEntropy_                         B.3 Code M n α β (既存、measurability 抜け)
    gaussianReal = (1/2)log(2πev)                B.4 capacity W := sSup ... (既存 Fintype 想定)
    (既存)
A.3 differentialEntropy_le_                     B.5 shannon_noisy_channel_coding_
    gaussian_of_variance_le                          theorem_general_full (既存 Fintype 壁)
    (既存、4-hypothesis 形)
A.4 gaussianReal_add_                           B.6 fano_inequality_measure_theoretic
    gaussianReal_of_indepFun (既存)                   (既存、continuous Y で再利用可)
                                                B.7 condMutualInfo_chain_rule + memoryless
                                                    _per_summand_bound (既存)
        ▲                                                       ▲
        │ closed-form 100%                                       │ Fintype 壁を越える必要
        │                                                       │
        └────────────────────────┬────────────────────────────────┘
                                 ▼
                  AWGN 専用 layer (本 plan 新規、~1000-1500 行)
                  ─────────────────────────────────────────
                  Phase A: awgnChannel + AwgnCode + closed-form bridge + awgnCapacity_eq
                  Phase B: achievability (F-1 hypothesis pass-through)
                  Phase C: converse (F-3 hypothesis pass-through)
                  Phase D: 主定理 sandwich
```

**鍵となる構造構築** (3 ファイル分離戦略の根拠 / 判断ログ #2 候補):

1. **`AWGN.lean` (~250-350 行)** — 定義 + 主定理 statement (sorry なし完成) + 撤退ライン
   hypothesis form の publish window。`awgnChannel` の measurability proof、`AwgnCode`
   構造、`awgnCapacity` 定義 + 等号 (`= (1/2) log(1+P/N)`)、`awgn_channel_coding_theorem`
   の sandwich wrapper。Phase A + Phase D の本体。**最小限の依存** (Achievability /
   Converse import なしで完結) → Tier 0 / Tier 1 ship 可能 (撤退ライン F-1 + F-2 + F-3 を
   全て発動した状態でも publish 価値あり)。

2. **`AWGNAchievability.lean` (~400-700 行)** — Phase B 本体。Cover-Thomas 9.2 の sphere
   packing / continuous joint typicality を hypothesis pass-through 形で
   `h_typicality` 引数に潰す **F-1 撤退ライン採用前提**。実体 (sphere packing on `ℝⁿ`、
   `EuclideanSpace ℝ (Fin n)` 上の球殻 volume、Gaussian random codebook) は別 plan
   (`awgn-achievability-typicality-plan.md`) に切り出し。**`Common2026/Shannon/
   ChannelCodingAchievability.lean` の discrete 版 (`Fintype α`) を構造的に参考にするが
   import しない** (型クラス壁により直接 reuse 不可)。

3. **`AWGNConverse.lean` (~300-450 行)** — Phase C 本体。`fano_inequality_measure_theoretic`
   (`Common2026/Fano/Measure.lean`、`X := Fin M` finite + `Y := Fin n → ℝ` continuous で
   再利用可、§危険 5 参照) + `condMutualInfo_chain_rule` + per-letter max-entropy
   (`differentialEntropy_le_gaussian_of_variance_le`、4-hypothesis 形、`h_ent_int` のみ
   F-3 で外出し) の連鎖。**`Common2026/Shannon/ChannelCodingConverseGeneralComplete.lean`
   から `channel_coding_converse_general_memoryless` の代わりに **per-letter bound 部分の
   schema を copy + Gaussian max-entropy substitution**。Fano 部分は `X := Fin M`,
   `Y := Fin n → ℝ` で既存 `fano_inequality_measure_theoretic` を直接呼ぶ (X 側の
   `Fintype + MeasurableSingletonClass` 要求は `Fin M` で自動充足、Y 側に制約なし)。

**Mathlib-shape-driven な定義選択** (在庫 §H + CLAUDE.md "Mathlib-shape-driven Definitions"):

- **`awgnChannel N : Channel ℝ ℝ`** は `toFun x := gaussianReal x N` で **Mathlib
  `gaussianReal_add_gaussianReal_of_indepFun` の結論形に直結**。`mean := x` (信号
  シフト) と `variance := N` (noise power) の 2 引数で書けば、`output = input + noise` の
  典型形 `Y = X + Z` が `outputDistribution (gaussianReal 0 P) (awgnChannel N) =
  gaussianReal 0 (P+N)` (`gaussianReal_conv_gaussianReal` 直接適用) に至る。textbook 形
  「`W(y|x) = (1/√(2πN)) exp(-(y-x)²/(2N))`」を直書きすると `gaussianPDF` への reshape
  が +50 行になるので**直接 measure 形を採用**。

- **`mutualInfoOfChannel p W : ℝ≥0∞`** (既存 `Common2026/Shannon/ChannelCoding.lean:84`、
  `klDiv` 形) を AWGN の closed form `(1/2) log(1+P/N)` に橋渡しする補題:
  - **理想形 (full bridge)**: `I = h(Y) - h(Y|X) = h(Y) - h(Z)` を mathlib `klDiv_compProd_eq_add`
    chain rule 経由で展開 → 200-400 行のリスク (§危険 5、Mathlib-shape-driven レッドフラグ
    「`f (compProd ...)` の reshape bridge」を探すパターン)。
  - **本 plan の採用形 (F-2 撤退ライン前提)**: `h_mi_bridge : (mutualInfoOfChannel
    (gaussianReal 0 P) (awgnChannel N)).toReal = differentialEntropy
    ((gaussianReal 0 P) ⊗ₘ (awgnChannel N)).snd - differentialEntropy (gaussianReal 0 N)`
    を hypothesis として publish の主定理 signature に追加。bridge 補題の構築は別 plan
    (`awgn-mi-bridge-plan.md`) に defer。**T1-B Chernoff `L-S2` / T1-C Cramér `L-C2` /
    T2-F `L-F1+L-F2` で確立した hypothesis pass-through pattern と同型**。

- **`awgnCapacity P N : ℝ`** は **`sSup ((mutualInfoOfChannel · awgnChannel) ''
  {p : E[X²] ≤ P})`** で `sSup` 直書き。**`Common2026/Shannon/ChannelCodingShannonTheorem.lean:102`
  の `capacity W` (`stdSimplex` 形、`Fintype α` 想定) は AWGN で適用不可なので新規定義**。
  `bddAbove` の上界 `(1/2) log(1+P/N)` を Gaussian input + F-2 hypothesis で取れば、
  `awgnCapacity_le_gaussian` + `awgnCapacity_ge_gaussian` で `awgnCapacity = (1/2) log(1+P/N)`
  の sandwich が組める。

### Approach 図

```
Phase 0 : Mathlib + Common2026 API 在庫                          ← 完了済 (inventory 643 行)
          ──────────────────────────────────────────────────────
Phase A : AWGN.lean — awgnChannel + AwgnCode + MI bridge + awgnCapacity 定義 + 等号
                                                                 ← 1-1.5 session (2-3h)
                                                                   = Tier 0 (~250-350 行)
          ←──── 撤退ライン F-2 (h_mi_bridge hypothesis) ────────→
          ──────────────────────────────────────────────────────
Phase B : AWGNAchievability.lean — F-1 hypothesis pass-through achievability
                                                                 ← 1-2 session (3-5h)
                                                                   = Tier 1 (~400-700 行)
          ←──── 撤退ライン F-1 (h_typicality hypothesis) ───────→
          ──────────────────────────────────────────────────────
Phase C : AWGNConverse.lean — F-3 hypothesis pass-through converse
                                                                 ← 1.5-2 session (3-5h)
                                                                   = Tier 1 (~300-450 行)
          ←──── 撤退ライン F-3 (h_per_letter_aux hypothesis) ───→
          ──────────────────────────────────────────────────────
Phase D : AWGN.lean 末尾 — awgn_channel_coding_theorem sandwich  ← 0.5 session (1h)
                                                                   = Tier 2 (~50-100 行)
          ──────────────────────────────────────────────────────
Phase V : verify (3 ファイル `lake env lean` clean + Common2026.lean 編入準備)
                                                                 ← 0.25 session (0.5h)
```

### 段階的 ship 設計 (Tier 0 / 1 / 2 / 3)

- **Tier 0** (~250-350 行, Phase A): `awgnChannel` + Markov instance + `AwgnCode` 構造 +
  `awgnCapacity` 定義 + `outputDistribution_gaussianInput` (= `gaussianReal 0 (P+N)`) +
  `awgnCapacity_eq` (F-2 hypothesis 形)。Phase A 完了で発生、`Common2026.lean` 編入 OK。
  **partial publish 価値あり** (closed-form capacity を hypothesis 形で publish、
  achievability / converse は次フェーズ)。
- **Tier 1** (~700-1200 行, Phase A + B + C): + `awgn_achievability` (F-1 hypothesis) +
  `awgn_converse` (F-3 hypothesis)。Phase B + C 完了で発生 = **本 plan の現実的到達点**
  (撤退ライン F-1 + F-2 + F-3 全採用、seed 規模 1000-1500 行に収まる)。
- **Tier 2** (~750-1300 行, Phase A + B + C + D): + `awgn_channel_coding_theorem` 主定理
  sandwich + Tendsto 形 (任意)。Phase D 完了 = **Cover-Thomas 9.1.1 + 9.1.2 完成形** (3
  hypothesis pass-through を保ったまま統合 publish)。
- **Tier 3 (任意 stretch)**: 撤退ライン F-1 / F-2 / F-3 のいずれかを discharge する別 plan
  (`awgn-achievability-typicality-plan.md` / `awgn-mi-bridge-plan.md` /
  `awgn-converse-aux-plan.md`)。**本 plan のスコープ外**、Tier 2 publish 後の派生 plan で。

### 規模見積もり (再掲、inventory §D + §E + §H より)

| 自作要素 | 想定行数 | Phase | ファイル |
|---|---|---|---|
| D.1 `awgnChannel` kernel + Markov instance | ~50-100 | A | `AWGN.lean` |
| D.6 `AwgnCode` 構造 + `toCode` 変換 | ~30-50 | A | `AWGN.lean` |
| D.3 `mutualInfoOfChannel` closed form (F-2 hypothesis form) | ~30-50 | A | `AWGN.lean` |
| D.2 `awgnCapacity` 定義 + bddAbove + nonneg + 等号 | ~100-200 | A | `AWGN.lean` |
| `outputDistribution_gaussianInput` (`= gaussianReal 0 (P+N)`) | ~30-50 | A | `AWGN.lean` |
| D.4 Achievability (F-1 hypothesis form + sphere packing schema) | ~400-700 | B | `AWGNAchievability.lean` |
| D.5 Converse (Fano + chain rule + per-letter max-entropy with F-3) | ~300-450 | C | `AWGNConverse.lean` |
| `awgn_channel_coding_theorem` sandwich + Tendsto | ~50-100 | D | `AWGN.lean` |
| skeleton + imports + docstring + namespace (3 ファイル合計) | ~100-150 | A/B/C | 各 |
| **合計** | **~1090-1850** | | |

中央予測 **~1250 行** (roadmap 「1000-1500 行」中央)。撤退ライン F-1 + F-2 + F-3 全採用で
**~1000-1300 行**、F-2 単独採用で ~1400-1600 行、F-1 + F-2 + F-3 を全 discharge して
本 plan 完結なら ~1800-2200 行 (本 plan のスコープを超えるため discharge は Tier 3 plan へ)。

### ファイル構成 (Phase V 完了想定)

```
Common2026/Shannon/
  AWGN.lean                    ← 新規 (Phase A + D、~250-450 行 = Tier 0 + main wrapper)
  AWGNAchievability.lean       ← 新規 (Phase B、~400-700 行、F-1 hypothesis form)
  AWGNConverse.lean            ← 新規 (Phase C、~300-450 行、F-3 hypothesis form)
  DifferentialEntropy.lean     ← 既存 1010 行、変更なし (再利用元)
  ChannelCoding.lean           ← 既存、変更なし (`Channel`, `Code`, `mutualInfoOfChannel`)
  BlockwiseChannel.lean        ← 既存、変更なし (`Channel.toBlock` の measurability proof
                                  schema 参考)
  MutualInfo.lean              ← 既存 (`mutualInfo` typed RV 形、Phase C で利用)
  CondMutualInfo.lean          ← 既存 (chain rule、Phase C で利用)
  MIChainRule.lean             ← 既存 (per-letter bound、Phase C で利用)
Common2026/Fano/
  Measure.lean                 ← 既存 (`fano_inequality_measure_theoretic`、Phase C で
                                  X := Fin M, Y := Fin n → ℝ で直接再利用)
Common2026.lean                ← `import Common2026.Shannon.AWGN` +
                                  `import Common2026.Shannon.AWGNAchievability` +
                                  `import Common2026.Shannon.AWGNConverse` を追記
                                  (Phase V、**オーケストレータが最後にまとめて編集**)
```

**新規 import (`AWGN.lean`、CLAUDE.md `Import Policy` 厳守、`import Mathlib` は使わない)**:

```lean
import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.BlockwiseChannel
import Common2026.Shannon.DifferentialEntropy
import Common2026.Shannon.MutualInfo
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Group.Convolution
```

**追加 import (`AWGNAchievability.lean`)**:

```lean
import Common2026.Shannon.AWGN
import Common2026.Shannon.ChannelCodingAchievability  -- schema 参考、直接 reuse は不可
-- (sphere packing 用) Mathlib.MeasureTheory.Measure.Lebesgue.EuclideanSpace 等は
-- F-1 hypothesis form では不要 (実体は別 plan へ defer)
```

**追加 import (`AWGNConverse.lean`)**:

```lean
import Common2026.Shannon.AWGN
import Common2026.Shannon.CondMutualInfo
import Common2026.Shannon.MIChainRule
import Common2026.Fano.Measure                      -- fano_inequality_measure_theoretic
import Common2026.Shannon.ChannelCodingConverseGeneralComplete  -- schema 参考のみ、
                                                                  -- Fintype 壁あり再利用不可
```

## 依存関係

完了済 / 利用可:

- [x] **Mathlib `Probability.Distributions.Gaussian.Real`** (inventory §A.1-A.3):
  `gaussianReal`, `gaussianPDFReal`, `gaussianPDF`, `rnDeriv_gaussianReal`,
  **`gaussianReal_conv_gaussianReal`** (最重要、`Real.lean:613`、`(gaussianReal m₁ v₁) ∗
  (gaussianReal m₂ v₂) = gaussianReal (m₁+m₂) (v₁+v₂)`),
  **`gaussianReal_add_gaussianReal_of_indepFun`** (typed RV 形、`Real.lean:624`、
  `P.map (X + Y) = gaussianReal (m₁+m₂) (v₁+v₂)`),
  `gaussianReal_absolutelyContinuous`, `variance_id_gaussianReal`,
  `integral_id_gaussianReal`, `memLp_id_gaussianReal'`,
  `integral_gaussianReal_eq_integral_smul`, `gaussianReal_map_add_const`,
  `instIsProbabilityMeasureGaussianReal`
- [x] **Mathlib `Probability.Distributions.Gaussian.Basic`**: `IsGaussian`,
  `isGaussian_gaussianReal`, `isGaussian_conv`, `IsGaussian.toIsProbabilityMeasure`
- [x] **Mathlib `Probability.Distributions.Gaussian.Multivariate`**: `stdGaussian`,
  `map_pi_eq_stdGaussian`, `IsGaussian.memLp_two_id` (Phase B sphere packing 想定だが
  本 plan では F-1 hypothesis form で defer)
- [x] **Mathlib `Probability.Kernel.*`**: `Kernel`, `IsMarkovKernel`, `IsFiniteKernel`,
  `IsSFiniteKernel`, `Measure.compProd` (`⊗ₘ`), `Kernel.compProd` (`⊗ₖ`),
  `IsMarkovKernel.compProd`, `compProd_apply_prod` (rectangular)
- [x] **Mathlib `Probability.Kernel.CondDistrib`** (inventory §C.3、§危険 1):
  `condDistrib`, `compProd_map_condDistrib`, `instIsMarkovKernelCondDistrib`
  (前提 `[StandardBorelSpace Ω] [Nonempty Ω]` は output 側 = `ℝ` で自動充足、`Fin n → ℝ`
  は要確認)
- [x] **Mathlib `Probability.Independence.Basic`**: `IndepFun`,
  `IndepFun.map_add_eq_map_conv_map₀'` (typed RV 形の畳み込み)
- [x] **Mathlib `Probability.Moments.Variance`**: `variance`, `evariance`,
  `variance_eq_integral` (Bochner 形)
- [x] **Mathlib `MeasureTheory.Group.Convolution`**: `Measure.mconv` /
  `Measure.conv` (`∗`)
- [x] **`Common2026/Shannon/DifferentialEntropy.lean`** (1010 行):
  `differentialEntropy`, `differentialEntropy_eq_integral_withDensity`,
  **`differentialEntropy_gaussianReal`** (最重要、`= (1/2) log(2πev)`),
  **`differentialEntropy_le_gaussian_of_variance_le`** (最重要、4-hypothesis 形、
  Cover-Thomas 8.6.1 max-entropy 主定理、Phase C per-letter bound の核),
  `klDiv_gaussianReal_gaussianReal_eq` (Gaussian × Gaussian KL closed form)
- [x] **`Common2026/Shannon/ChannelCoding.lean`** (`Channel α β := Kernel α β`,
  `jointDistribution`, `outputDistribution`, `mutualInfoOfChannel`, `Code M n α β`
  bundle、`Code.errorProbAt`, `averageErrorProb`)
- [x] **`Common2026/Shannon/BlockwiseChannel.lean`**: `Channel.toBlock` の measurability
  proof schema (`BlockwiseChannel.lean:77-95` あたり、`awgnChannel.measurable'`
  実装の参考)
- [x] **`Common2026/Shannon/MutualInfo.lean:36`**: `mutualInfo μ Xs Yo` (typed RV、
  KL 形、Phase C で `X^n` と `Y^n` の MI を組むときに利用)
- [x] **`Common2026/Shannon/CondMutualInfo.lean`** + `MIChainRule.lean`: `condMutualInfo`,
  `condMutualInfo_chain_rule_X_2var` (Phase C chain rule per-letter 連鎖の核)
- [x] **`Common2026/Fano/Measure.lean`**: `fano_inequality_measure_theoretic` (Phase C
  で `X := Fin M`, `Y := Fin n → ℝ` で直接再利用)

**参考 (import しない / schema のみ参照)**:

- `Common2026/Shannon/ChannelCodingAchievability.lean` (discrete `Fintype α` 想定、
  schema 参考のみ — joint typical decoder の構造は流用するが、`jointlyTypicalSet` 連続版
  は別 plan へ defer)
- `Common2026/Shannon/ChannelCodingConverseGeneralComplete.lean` (`Fintype α` +
  `MeasurableSingletonClass α` 想定、schema 参考のみ — chain rule + per-letter bound 連鎖
  の構造を流用、Gaussian max-entropy substitution は本 plan で実装)
- `Common2026/Shannon/ChannelCodingShannonTheoremFullDischarge.lean` (`Fintype α`
  必須、AWGN 適用不可)

---

## Phase 0 — Mathlib + Common2026 API 在庫 ✅

完了 ([`awgn-mathlib-inventory.md`](awgn-mathlib-inventory.md), 643 行)。

主結論:

- **Gaussian 精密計算は 100% Mathlib 既存** — `gaussianReal_conv_gaussianReal`,
  `gaussianReal_add_gaussianReal_of_indepFun`, `variance_id_gaussianReal`,
  `rnDeriv_gaussianReal` ですべて足りる
- **continuous entropy + max-entropy は Common2026 既存** —
  `differentialEntropy_gaussianReal` (`= (1/2) log(2πev)`) と
  `differentialEntropy_le_gaussian_of_variance_le` (4-hypothesis 形) が converse の
  per-letter bound そのまま
- **AWGN 専用 6 ピース** (`awgnChannel`, `AwgnCode`, MI closed form bridge, `awgnCapacity`
  定義 + 等号, achievability, converse) **が自作必要**
- **最大リスク**: discrete `Code` の measurability bundle 不在 (`α := ℝ` で
  `MeasurableSingletonClass` 偽), `mutualInfo` の KL 形 vs `h(Y) - h(Y|X)` 形の
  bridge 補題不在 (200-400 行リスク、撤退 F-2 で回避可)
- **撤退ライン候補 3 本** (F-1 achievability hypothesis, F-2 MI bridge hypothesis,
  F-3 per-letter ent_int hypothesis)
- **本 plan は撤退ライン F-1 + F-2 + F-3 の組合せ発動を想定**して計画 (seed 規模
  1000-1500 行に収めるため、判断ログ #1 候補)

### Phase 0 内で確定する判断 (判断ログ #1 + #2 候補)

Phase A 着手直前に以下を確定:

- [ ] **判断 #1**: `mutualInfo` redefinition vs bridge 補題の選択。
  - **option (a) — bridge 補題 (F-2 不採用)**: `mutualInfoOfChannel` の現定義
    (`klDiv (μ.map (X,Y)) ((μ.map X).prod (μ.map Y))`) を保持し、
    `I = h(Y) - h(Y|X)` 形への bridge 補題を 200-400 行で構築。
  - **option (b) — F-2 撤退ライン採用 (本 plan 推奨)**: bridge を hypothesis
    pass-through 形 (`h_mi_bridge`) で外出し、bridge 補題は別 plan (`awgn-mi-bridge-plan.md`)
    に defer。**規模 1000-1500 行に収める唯一の現実解**。
  - **option (c) — redefinition (リスク高)**: `mutualInfo` 定義を `h(Y) - h(Y|X)`
    形に変更。**既存 publish 済の Stein / Sanov / Chernoff / Shannon main theorem 等
    広範囲に破壊的影響、本 plan 範囲外で実施不可**。
  - **判断**: **option (b) を採用予定** (判断ログ #1 で記録、Phase A 着手時)。
- [ ] **判断 #2**: 3 ファイル分離 vs 単一ファイル。
  - **option (a) — 単一 `AWGN.lean` (~1250 行)**: 全 Phase を 1 ファイルに集約。
    LSP 診断と incremental compile が遅くなる懸念、`private` 補助補題が混在しやすい
    (CLAUDE.md `private` は file-scoped)。
  - **option (b) — 3 ファイル分離 (本 plan 推奨)**: `AWGN.lean` (定義 + 主定理 wrapper)
    + `AWGNAchievability.lean` + `AWGNConverse.lean`。Phase 単位の ship が独立、
    撤退ラインを Phase 単位で発動可能、Tier 0 publish (定義のみ) で Common2026.lean
    編入可能。
  - **判断**: **option (b) を採用予定** (判断ログ #2 で記録、Phase A 着手時)。
- [ ] **判断 #3**: `AwgnCode` 構造体の field 確定 (`encoder` / `decoder` /
  `decoder_meas` / `power_constraint` の 4 field か、`encoder_meas` を追加して 5 field か)。
  encoder は `Fin M → (Fin n → ℝ)` で定義域 `Fin M` finite ⇒ `Measurable encoder`
  自動充足 (§危険 2)、bundle 不要。**4 field で確定予定**。

---

## Phase A — `AWGN.lean` (awgnChannel + AwgnCode + closed-form bridge + awgnCapacity) 📋

### スコープ

`Common2026/Shannon/AWGN.lean` 新規作成 (~250-350 行)。

- skeleton write (全主定理 `:= by sorry`)
- `awgnChannel` kernel 定義 + Markov instance + measurability proof
- `AwgnCode` 構造 + `toCode` 変換
- `outputDistribution_gaussianInput` (= `gaussianReal 0 (P+N)`)
- F-2 hypothesis 形 `mutualInfoOfChannel_gaussianInput_closed_form`
- `awgnCapacity P N` 定義 + `bddAbove` + `nonneg`
- `awgnCapacity_ge_gaussian` (achievability of Gaussian input、F-2 hypothesis 利用)
- `awgnCapacity_le_gaussian` (converse via Gaussian max-entropy)
- `awgnCapacity_eq` (sandwich)

**proof-log**: yes (`proof-log-awgn-phaseA.md` を Phase A 完了時に append)。

### Done 条件

- `Common2026/Shannon/AWGN.lean` 新規作成
- 上記 8 主定理 / 主補題が 0 sorry / 0 warning で publish (Phase B/C/D 主定理は
  `:= by sorry` skeleton 残し OK)
- `lake env lean Common2026/Shannon/AWGN.lean` clean (Phase A 本体 0 sorry、他 sorry 残し)
- 判断ログ #1, #2, #3 を append

### ステップ

- [ ] **A-0 skeleton write** (`AWGN.lean` 全主定理 + 補助補題を `:= by sorry` で並べる、
  inventory §H の skeleton 200 行を base にする)。LSP 診断で type-check OK 確認 (CLAUDE.md
  "Skeleton-driven Development")。imports は §依存関係 の `AWGN.lean` リストのみ。

- [ ] **A-1 `awgnChannel` kernel 定義 + measurability** (`D.1`、~50-100 行):
  ```lean
  noncomputable def awgnChannel (N : ℝ≥0) :
      InformationTheory.Shannon.ChannelCoding.Channel ℝ ℝ where
    toFun x := gaussianReal x N
    measurable' := by
      -- 戦略 1 (Mathlib-shape-driven, 推奨):
      --   gaussianReal m v は `if v = 0 then Measure.dirac m else volume.withDensity (gaussianPDF m v)`
      --   分岐に対し、`Measurable (fun m => gaussianReal m v)` を `MeasurableSpace (Measure ℝ)`
      --   の generator (`fun s : Set ℝ => fun μ => μ s` の measurability) で組む。
      -- 戦略 2 (BlockwiseChannel.lean:77 schema 流用):
      --   `Channel.toBlock` の measurability proof を参考に
      --   `Measurable.measure_of_isPiSystem_of_isProbabilityMeasure` 経由で組む。
      sorry
  ```
  **落とし穴**: `gaussianReal m v` の `m`-measurability は Mathlib に直接 lemma が
  ない可能性大 (要 loogle 確認)。`gaussianPDFReal m v x` の `m`-連続性 ⇒ measurability
  経由が王道。20-50 行で済む見込み、超えれば judgement log で記録 (`L-A1` 候補?)。

- [ ] **A-2 `awgnChannel.instIsMarkovKernel`** (~5-10 行):
  ```lean
  instance awgnChannel.instIsMarkovKernel (N : ℝ≥0) : IsMarkovKernel (awgnChannel N) where
    isProbabilityMeasure x := by
      show IsProbabilityMeasure (gaussianReal x N)
      infer_instance
  ```
  `instIsProbabilityMeasureGaussianReal` (Mathlib `Real.lean:209`) を `infer_instance`
  で拾うだけ。

- [ ] **A-3 `AwgnCode` 構造 + `toCode` 変換** (`D.6`、~30-50 行):
  ```lean
  structure AwgnCode (M n : ℕ) (P : ℝ) where
    encoder : Fin M → (Fin n → ℝ)
    decoder : (Fin n → ℝ) → Fin M
    decoder_meas : Measurable decoder
    power_constraint : ∀ m : Fin M, (∑ i : Fin n, (encoder m i)^2) ≤ (n : ℝ) * P

  noncomputable def AwgnCode.toCode {M n : ℕ} {P : ℝ} (c : AwgnCode M n P) :
      InformationTheory.Shannon.ChannelCoding.Code M n ℝ ℝ where
    encoder := c.encoder
    decoder := c.decoder
  ```
  encoder の measurability は `Fin M` finite ⇒ `Measurable encoder` 自動充足 (§危険 2)、
  bundle 不要 (判断 #3 で確定)。

- [ ] **A-4 `outputDistribution_gaussianInput`** (~30-50 行):
  ```lean
  theorem outputDistribution_gaussianInput (P N : ℝ≥0) :
      InformationTheory.Shannon.ChannelCoding.outputDistribution
          (gaussianReal 0 P) (awgnChannel N)
        = gaussianReal 0 (P + N) := by
    -- outputDistribution := (p ⊗ₘ W).snd
    -- p = gaussianReal 0 P, W x = gaussianReal x N
    -- 戦略: (gaussianReal 0 P) ⊗ₘ (awgnChannel N) のテスト関数 ∫ f y d... を計算し、
    --       gaussianReal_conv_gaussianReal (m₁+m₂, v₁+v₂) = gaussianReal 0 (P+N) と一致を示す
    -- もしくは `IndepFun X Z, X ∼ 𝒩(0,P), Z ∼ 𝒩(0,N)` の `X+Z ∼ 𝒩(0,P+N)` を
    -- ambient で構成し outputDistribution と equal を示す
    sorry
  ```
  落とし穴: `outputDistribution = (μ ⊗ₘ W).snd` の RHS を `(μ ∗ ν)` 形に書き換える
  bridge が必要。Mathlib に直接 `Measure.compProd.snd_eq_conv` のような lemma が
  あるか要 loogle 確認。なければ手動で `compProd_apply_prod` + `gaussianReal_apply`
  を組み合わせる ~30 行。

- [ ] **A-5 F-2 hypothesis 形 `mutualInfoOfChannel_gaussianInput_closed_form`** (~30-50 行):
  ```lean
  theorem mutualInfoOfChannel_gaussianInput_closed_form
      (P N : ℝ≥0) (hP : (P : ℝ) ≠ 0) (hN : (N : ℝ) ≠ 0)
      (h_mi_bridge :
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              (gaussianReal 0 P) (awgnChannel N)).toReal
            = Common2026.Shannon.differentialEntropy (gaussianReal 0 (P + N))
                - Common2026.Shannon.differentialEntropy (gaussianReal 0 N)) :
      (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
          (gaussianReal 0 P) (awgnChannel N)).toReal
        = (1/2) * Real.log (1 + (P : ℝ) / (N : ℝ)) := by
    rw [h_mi_bridge]
    rw [differentialEntropy_gaussianReal _ (by exact_mod_cast (add_pos ...))]
    rw [differentialEntropy_gaussianReal _ hN]
    -- (1/2) log(2πe(P+N)) - (1/2) log(2πeN) = (1/2) log((P+N)/N) = (1/2) log(1 + P/N)
    ring_nf
    -- log 算法 (`Real.log_div`, `Real.log_mul` 等)
    sorry
  ```
  `differentialEntropy_gaussianReal` (`DifferentialEntropy.lean:406`、結論
  `= (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)`) を 2 回引いて差を取る純算術。
  20-30 行。

- [ ] **A-6 `awgnCapacity` 定義 + 補助** (`D.2` 前半、~50-100 行):
  ```lean
  noncomputable def awgnCapacity (P : ℝ) (N : ℝ≥0) : ℝ :=
    sSup ((fun p : Measure ℝ =>
            (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
                p (awgnChannel N)).toReal) ''
          { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P })

  theorem awgnCapacity_nonneg (P : ℝ) (hP : 0 ≤ P) (N : ℝ≥0) :
      0 ≤ awgnCapacity P N := by sorry
    -- 戦略: dirac 0 が image に入り、I(dirac 0; W) = 0 (退化) ⇒ sSup ≥ 0

  theorem awgnCapacity_bddAbove (P : ℝ) (N : ℝ≥0) (hP : 0 ≤ P) (hN : (N : ℝ) ≠ 0) :
      BddAbove ((fun p : Measure ℝ =>
                  (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
                      p (awgnChannel N)).toReal) ''
                { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P }) := by sorry
    -- 戦略: Gaussian max-entropy で上界 (1/2) log(1 + P/N) を取る (A-7 と循環、要分離)
  ```

- [ ] **A-7 `awgnCapacity_ge_gaussian` (achievability of Gaussian input)** (~30-50 行):
  ```lean
  theorem awgnCapacity_ge_gaussian
      (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
      (h_mi_bridge_gauss :
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              (gaussianReal 0 P.toNNReal) (awgnChannel N)).toReal
            = (1/2) * Real.log (1 + P / (N : ℝ))) :
      (1/2) * Real.log (1 + P / (N : ℝ)) ≤ awgnCapacity P N := by
    -- 戦略: gaussianReal 0 P.toNNReal が { p | IsProbabilityMeasure ∧ ∫ x², ≤ P } に入る
    --       ことを variance_id_gaussianReal で確認 → A-5 hypothesis 形を直接適用
    sorry
  ```

- [ ] **A-8 `awgnCapacity_le_gaussian` (converse via Gaussian max-entropy)** (~100-150 行):
  ```lean
  theorem awgnCapacity_le_gaussian
      (P : ℝ) (hP : 0 ≤ P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
      (h_max_ent :
          ∀ (p : Measure ℝ) [IsProbabilityMeasure p], (∫ x, x^2 ∂p ≤ P) →
            (mutualInfoOfChannel p (awgnChannel N)).toReal
              ≤ (1/2) * Real.log (1 + P / (N : ℝ))) :
      awgnCapacity P N ≤ (1/2) * Real.log (1 + P / (N : ℝ)) := by
    -- 戦略: sSup 上界の標準形 (csSup_le_iff + 任意の image element ≤ bound)
    sorry
  ```
  `h_max_ent` 自体の証明は `differentialEntropy_le_gaussian_of_variance_le`
  (`DifferentialEntropy.lean:510`、4-hypothesis 形) を per-input law に適用すれば
  derive 可だが、本 plan では Phase C で converse 本体と整合させる形で 1 サイクル
  証明する (Phase A では `h_max_ent` も hypothesis として残す option あり、Phase A 内で
  closed する option もあり、judgement #4 候補)。

- [ ] **A-9 `awgnCapacity_eq` sandwich** (~10-20 行):
  ```lean
  theorem awgnCapacity_eq
      (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
      (h_mi_bridge_gauss : ...)
      (h_max_ent : ...) :
      awgnCapacity P N = (1/2) * Real.log (1 + P / (N : ℝ)) := by
    apply le_antisymm
    · exact awgnCapacity_le_gaussian P hP.le N hN h_max_ent
    · exact awgnCapacity_ge_gaussian P hP N hN h_mi_bridge_gauss
  ```

- [ ] **A-10 verify**: `lake env lean Common2026/Shannon/AWGN.lean` clean (Phase A 本体
  0 sorry、Phase B/C/D は `sorry` 残し)。判断ログ #1, #2, #3 を append (`option (b)`
  F-2 採用 / `option (b)` 3 ファイル分離 / `AwgnCode` 4 field 確定)。

### 工数感

~250-350 行 (skeleton ~50 + A-1 ~80 + A-2 ~5 + A-3 ~40 + A-4 ~40 + A-5 ~30 + A-6 ~80 +
A-7 ~40 + A-8 ~120 + A-9 ~15)。1-1.5 session。proof-log `yes`。

### 失敗時 fallback

- **A-1 `awgnChannel.measurable'` proof が 100 行を超える**: Mathlib に `gaussianReal`
  の `m`-measurability 直接 lemma がない場合、`gaussianPDFReal m v x` の `m`-連続性
  経由で組む必要があり一定行数。それでも超えるなら **Phase A の `awgnChannel` を
  hypothesis form** (`h_awgn_measurable : Measurable (fun x => gaussianReal x N)` を
  引数として外出し) で publish し、measurability proof は別 plan
  (`awgn-kernel-measurability-plan.md`) に defer。
- **A-4 `outputDistribution_gaussianInput` の bridge が肥大**: Mathlib に
  `(p ⊗ₘ W).snd = p ∗ ν` のような直接 lemma がない場合、**Phase A 内では
  `gaussianReal 0 (P+N)` 同一視を hypothesis form** で外出し、Phase B/C で実体を
  必要に応じて discharge (F-2 と同じ pattern)。

---

## Phase B — `AWGNAchievability.lean` (F-1 hypothesis pass-through achievability) 📋

### スコープ

`Common2026/Shannon/AWGNAchievability.lean` 新規作成 (~400-700 行)。

撤退ライン **F-1 採用前提**: continuous joint typicality / sphere packing の実体は
別 plan (`awgn-achievability-typicality-plan.md`) に defer し、本 plan では
**hypothesis pass-through 形で `awgn_achievability` を publish**。

**proof-log**: yes (`proof-log-awgn-phaseB.md` を Phase B 完了時に append)。

### Done 条件

- `Common2026/Shannon/AWGNAchievability.lean` 新規作成
- `awgn_achievability` 主定理 (F-1 hypothesis form) publish
- `lake env lean Common2026/Shannon/AWGNAchievability.lean` clean

### ステップ

- [ ] **B-0 skeleton write** (`AWGNAchievability.lean`、imports は §依存関係 の
  `AWGNAchievability.lean` リストのみ)。

- [ ] **B-1 F-1 hypothesis predicate 定義** (~30-50 行):
  ```lean
  /-- **AWGN continuous joint-typicality hypothesis** (Cover-Thomas 9.2 schema).
  実体 = sphere packing on `ℝⁿ` + Gaussian random codebook + continuous AEP。
  本 hypothesis を discharge するのは別 plan
  (`awgn-achievability-typicality-plan.md`)。 -/
  def IsAwgnTypicalityHypothesis (P : ℝ) (N : ℝ≥0) : Prop :=
    ∀ {R : ℝ}, 0 < R → R < (1/2) * Real.log (1 + P / (N : ℝ)) →
    ∀ {ε : ℝ}, 0 < ε →
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
        ∀ m, (c.toCode.errorProbAt (awgnChannel N) m).toReal < ε
  ```
  これを `Cramer.lean` `h_tilted_lower` / `FisherInfo.lean` `IsRegularDeBruijnHyp` /
  separation-theorem `h_typicality` の同型 patten で publish。

- [ ] **B-2 (任意) F-1 hypothesis を構成的に discharge する schema lemma 群** (~200-400 行):
  - **schema 1**: Gaussian random codebook construction (`gaussianCodebook M n P` =
    `Fin M → (Fin n → ℝ)` の i.i.d. `𝒩(0, P-δ)` sample)
  - **schema 2**: continuous joint typical set on `ℝⁿ × ℝⁿ` (Mathlib `Metric.sphere` +
    `EuclideanSpace ℝ (Fin n)` volume)
  - **schema 3**: 3 つの continuous AEP bounds (sphere volume / Gaussian tail decay /
    union bound on M codewords)
  - **これらは F-1 採用なら本 plan ではスケルトンのみ** (`:= by sorry`) で残し、
    Tier 3 plan (`awgn-achievability-typicality-plan.md`) で discharge。
  - **本 plan で具体 publish するのは `IsAwgnTypicalityHypothesis` の定義 + `awgn_achievability`
    主定理 (hypothesis を pass-through するだけの薄い wrapper)** のみ。

- [ ] **B-3 `awgn_achievability` 主定理 (F-1 hypothesis form)** (~50-100 行):
  ```lean
  theorem awgn_achievability
      (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
      (h_typicality : IsAwgnTypicalityHypothesis P N)
      {R : ℝ} (hR_pos : 0 < R) (hR : R < (1/2) * Real.log (1 + P / (N : ℝ)))
      {ε : ℝ} (hε : 0 < ε) :
      ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
          ∀ m, (c.toCode.errorProbAt (awgnChannel N) m).toReal < ε :=
    h_typicality hR_pos hR hε
  ```
  これは `h_typicality` を pass-through するだけの 1 行 proof。**F-1 撤退ライン の
  本体**。

- [ ] **B-4 (任意) Tendsto 形 corollary** (~30-50 行):
  Achievability の rate `R` を `R < C` で動かしたときの Tendsto 形 (Cover-Thomas 9.1.1
  の漸近形)。`tendsto_atTop_of_eventually_le` 系で書ける ~20-30 行。**本 plan の
  スコープ外**、Phase D wrapper で取り扱う option あり。

- [ ] **B-5 verify**: `lake env lean Common2026/Shannon/AWGNAchievability.lean` clean。

### 工数感

**F-1 採用前提で ~400-700 行** (skeleton ~50 + B-1 ~50 + B-2 schema lemma 群
~200-400 (`:= by sorry` 残しの skeleton で本 plan には counted されない) +
B-3 ~50 + B-4 ~30 + plumbing ~30)。

- F-1 完全採用 (B-2 を全て `:= by sorry` で残す): **~150-200 行**
- F-1 部分採用 (B-2 の一部を discharge): ~300-500 行
- F-1 不採用 (B-2 完全 discharge): **~800-1500 行 (本 plan のスコープを超えるため別 plan 必須)**

**1-2 session**。proof-log `yes`。

### 失敗時 fallback

- **F-1 完全採用でも `IsAwgnTypicalityHypothesis` 定義の引数整合が崩れる**: hypothesis
  の形を Tier 3 plan からの逆算で `_hM_lb` の不等号方向、`ε` の引数順序、
  `c.toCode.errorProbAt` vs `c.errorProbAt` (AwgnCode 直接 method を追加する場合) で
  検討 → judgement log で確定。
- **B-2 schema lemma 群 (sphere volume / Gaussian tail) が hypothesis form に
  reduce できない**: Tier 3 plan に丸投げするだけで本 plan は終わる、特段の困難なし。

---

## Phase C — `AWGNConverse.lean` (F-3 hypothesis pass-through converse) 📋

### スコープ

`Common2026/Shannon/AWGNConverse.lean` 新規作成 (~300-450 行)。

Cover-Thomas 9.1.2 (converse) の Lean 化: `log M ≤ n · C + 1 + Pe log M` (Fano) →
chain rule per-letter → per-letter max-entropy bound `h(Y_i) ≤ (1/2) log(2πe(P+N))` →
`log M ≤ n · (1/2) log(1+P/N) + Pe · log(M-1) + binEntropy(Pe)`。

撤退ライン **F-3 採用前提**: per-letter max-entropy の `h_ent_int` (Integrable
`negMulLog (rnDeriv μ vol)`) は input law `μ_i` 個別 discharge できない可能性が高い
ため、converse 全体の hypothesis として外出し。

**proof-log**: yes (`proof-log-awgn-phaseC.md` を Phase C 完了時に append)。

### Done 条件

- `Common2026/Shannon/AWGNConverse.lean` 新規作成
- `awgn_converse` 主定理 (F-3 hypothesis form) publish
- `lake env lean Common2026/Shannon/AWGNConverse.lean` clean

### ステップ

- [ ] **C-0 skeleton write** (`AWGNConverse.lean`、imports は §依存関係 の
  `AWGNConverse.lean` リストのみ)。

- [ ] **C-1 F-3 hypothesis predicate 定義** (~30-50 行):
  ```lean
  /-- **Per-letter integrability hypothesis** for AWGN converse (Cover-Thomas 8.6.1
  の `differentialEntropy_le_gaussian_of_variance_le` 4-hypothesis 形のうち、`h_ent_int`
  に対応)。Input law `μ_i` ごとに `Integrable (negMulLog (rnDeriv μ_i vol)) volume` を
  要求する。本 hypothesis を discharge するのは別 plan (`awgn-converse-aux-plan.md`)。 -/
  def IsAwgnConverseIntegrableHyp (P : ℝ) (N : ℝ≥0) : Prop :=
    ∀ {n : ℕ} {M : ℕ} (c : AwgnCode M n P),
      ∀ i : Fin n, ∀ μ_i : Measure ℝ, [IsProbabilityMeasure μ_i] →
        μ_i ≪ volume →  -- absolutely continuous (input law w.r.t. Lebesgue)
        Integrable (fun y => Real.negMulLog ((μ_i.rnDeriv volume y).toReal)) volume
  ```

- [ ] **C-2 per-letter max-entropy specialization for AWGN output** (`D.5` 核、~80-120 行):
  ```lean
  theorem differentialEntropy_Yi_le_max_entropy_AWGN
      (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
      (P N : ℝ) (hP_pos : 0 < P) (hN_pos : 0 < N)
      (h_mean : ∫ y, y ∂μ = 0)
      (h_var_bound : ∫ y, y^2 ∂μ ≤ P + N)
      (h_var_int : Integrable (fun y => y^2) μ)
      (h_ent_int : Integrable
          (fun y => Real.negMulLog ((μ.rnDeriv volume y).toReal)) volume) :
      Common2026.Shannon.differentialEntropy μ
        ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (P + N)) := by
    -- 戦略: differentialEntropy_le_gaussian_of_variance_le を v := (P + N).toNNReal
    --       で適用、4 hypotheses を順に discharge
    apply Common2026.Shannon.differentialEntropy_le_gaussian_of_variance_le hμ 0
      (v := (P + N).toNNReal) (by positivity) h_mean
      (by simpa using h_var_bound) h_var_int h_ent_int
  ```
  `differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:510`、結論
  `differentialEntropy μ ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)`) を直接
  起動するだけ。

- [ ] **C-3 chain rule per-letter** (~80-120 行):
  ```lean
  /-- **Chain rule for AWGN output**: `I(X^n; Y^n) ≤ ∑ i, I(X_i; Y_i)` (memoryless). -/
  theorem mutualInfo_Xn_Yn_le_sum
      {n M : ℕ} (c : AwgnCode M n P) ... :
      (mutualInfo μ (jointRV c.encoder n) (jointRV ... n)).toReal
        ≤ ∑ i : Fin n, (mutualInfo μ (proj i ∘ encoder) (proj i ∘ output)).toReal := by
    -- 戦略: condMutualInfo_chain_rule_X_2var を n 回適用
    --       (Common2026/Shannon/MIChainRule.lean + CondMutualInfo.lean)
    sorry
  ```
  既存 `condMutualInfo_chain_rule_X_2var` (`Common2026/Shannon/MIChainRule.lean`) を
  reuse。**Fano Phase 3 の経験で `[StandardBorelSpace X]` `[Nonempty]` 等の
  type-class 整合に注意** (§危険 1)。

- [ ] **C-4 per-letter `I(X_i; Y_i) ≤ (1/2) log(1+P/N)`** (~50-80 行):
  ```lean
  theorem mutualInfo_Xi_Yi_le_capacity
      (μ : Measure Ω) ...
      (h_var_Xi : ∫ ω, (X_i ω)^2 ∂μ ≤ P)
      (h_indep_Zi : IndepFun X_i Z_i μ)
      (hZi_law : μ.map Z_i = gaussianReal 0 N)
      (h_per_letter_aux : IsAwgnConverseIntegrableHyp P N) :
      (mutualInfo μ X_i (X_i + Z_i)).toReal ≤ (1/2) * Real.log (1 + P / N) := by
    -- 戦略: I(X_i; Y_i) = h(Y_i) - h(Y_i | X_i) = h(Y_i) - h(Z_i)
    --       h(Y_i) ≤ C-2 (per-letter max-entropy) ≤ (1/2) log(2πe(P+N))
    --       h(Z_i) = differentialEntropy_gaussianReal = (1/2) log(2πeN)
    --       差 = (1/2) log((P+N)/N) = (1/2) log(1 + P/N)
    sorry
  ```
  **`I = h(Y) - h(Y|X) = h(Y) - h(Z)` の bridge** が必要なので、ここでも F-2 と同じ
  `h_mi_bridge_per_letter` を hypothesis 化する option あり (Phase C 内で local
  fallback、judgement log #X 候補)。

- [ ] **C-5 Fano + sum 連鎖** (~80-120 行):
  ```lean
  theorem awgn_converse
      (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
      (h_per_letter_aux : IsAwgnConverseIntegrableHyp P N)
      {M n : ℕ} (hM : 2 ≤ M) (c : AwgnCode M n P)
      (Pe : ℝ) (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
          (c.toCode.errorProbAt (awgnChannel N) m).toReal)) :
      Real.log M
        ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
          + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
    -- 戦略: fano_inequality_measure_theoretic で
    --         log M ≤ I(W; Ŵ) + binEntropy(Pe) + Pe · log(M-1)
    --       data processing で I(W; Ŵ) ≤ I(X^n; Y^n)
    --       C-3 chain rule で I(X^n; Y^n) ≤ ∑ I(X_i; Y_i)
    --       C-4 per-letter で ∑ I(X_i; Y_i) ≤ n · (1/2) log(1+P/N)
    sorry
  ```
  既存 `fano_inequality_measure_theoretic` (`Common2026/Fano/Measure.lean`) を
  `X := Fin M` (finite + `MeasurableSingletonClass` 自動)、`Y := Fin n → ℝ` (continuous、
  Fano の Y 側に制約なし) で直接呼ぶ。

- [ ] **C-6 verify**: `lake env lean Common2026/Shannon/AWGNConverse.lean` clean。

### 工数感

~300-450 行 (skeleton ~50 + C-1 ~40 + C-2 ~100 + C-3 ~100 + C-4 ~70 + C-5 ~100 +
plumbing ~30)。1.5-2 session。proof-log `yes`。

### 失敗時 fallback

- **C-3 chain rule の `condMutualInfo_chain_rule_X_2var` で `[StandardBorelSpace
  (Fin n → ℝ)]` `[Nonempty (Fin n → ℝ)]` が requirement されて自動推論されない**:
  Fano Phase 3 で同様の事故あり、`Fin n` の `[Nonempty]` instance を local で追加
  (`haveI : Nonempty (Fin n → ℝ) := ⟨0⟩` 等) で対処、judgement log で記録。
- **C-4 per-letter `I = h(Y) - h(Y|X)` bridge が Phase A の F-2 hypothesis と
  異なる shape で必要**: Phase C 内で `h_mi_bridge_per_letter` を追加 hypothesis として
  外出し (F-2 と同じ pattern で local 適用)、Phase D で main theorem の signature に
  集約。
- **C-5 Fano + sum 連鎖の type-class 整合が崩れる**: `Common2026/Shannon/
  ChannelCodingConverseGeneralComplete.lean:474` の `channel_coding_converse_general_memoryless`
  proof を schema 参考に `Fintype α` → `α := ℝ` への adapt が必要、最大 +50-80 行。
  judgement log で記録。

---

## Phase D — 主定理 wrapper (`AWGN.lean` 末尾) 📋

### スコープ

`AWGN.lean` 末尾に `awgn_channel_coding_theorem` (achievability + converse + closed-form
capacity の sandwich) を追加 (~50-100 行)。3 撤退ライン hypothesis を統合 signature に
集約。

**proof-log**: no (skeleton 揃った後の整地)。

### Done 条件

- `awgn_channel_coding_theorem` 主定理 publish (Tier 2 完成形)
- (任意) Tendsto 形 corollary (`awgn_capacity_tendsto`、`(1/n) log M_n → (1/2) log(1+P/N)`)
- (任意) `DotEq` corollary (`Asymptotic.lean` の `DotEq` を利用、本 plan の主定理は
  `Tendsto` でないため optional)
- `lake env lean Common2026/Shannon/AWGN.lean` clean (0 sorry, 0 warning)

### ステップ

- [ ] **D-1 `awgn_channel_coding_theorem` sandwich** (~30-50 行):
  ```lean
  theorem awgn_channel_coding_theorem
      (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
      (h_typicality : IsAwgnTypicalityHypothesis P N)
      (h_mi_bridge :
          (mutualInfoOfChannel (gaussianReal 0 P.toNNReal) (awgnChannel N)).toReal
            = differentialEntropy (gaussianReal 0 (P.toNNReal + N))
                - differentialEntropy (gaussianReal 0 N))
      (h_per_letter_aux : IsAwgnConverseIntegrableHyp P N)
      {R : ℝ} (hR_pos : 0 < R) (hR_lt_C : R < (1/2) * Real.log (1 + P / (N : ℝ)))
      {ε : ℝ} (hε : 0 < ε) :
      ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
          ∀ m, (c.toCode.errorProbAt (awgnChannel N) m).toReal < ε :=
    awgn_achievability P hP N hN h_typicality hR_pos hR_lt_C hε
  ```
  本体は `awgn_achievability` を呼ぶだけ (converse は `M ≤ ...` 形で別 corollary に
  分離する option もあり)。

- [ ] **D-2 (任意) Tendsto 形 corollary** (~20-30 行):
  ```lean
  theorem awgn_capacity_tendsto
      (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
      (h_typicality : IsAwgnTypicalityHypothesis P N)
      (h_mi_bridge : ...)
      (h_per_letter_aux : IsAwgnConverseIntegrableHyp P N) :
      Tendsto (fun n => (M_n : ℝ).log / n) atTop (𝓝 ((1/2) * Real.log (1 + P / N))) := ...
  ```
  Cover-Thomas 9.1.1 + 9.1.2 の漸近形。`tendsto_of_le_liminf_of_limsup_le` で
  achievability `R < C` と converse `R > C ⇒ error stays bounded away from 0` を
  sandwich。本 plan のスコープ外で OK、後続 plan に defer。

- [ ] **D-3 final verify**: `lake env lean Common2026/Shannon/AWGN.lean` clean (0 sorry,
  0 warning)、`lake env lean Common2026/Shannon/AWGNAchievability.lean` clean、
  `lake env lean Common2026/Shannon/AWGNConverse.lean` clean。

### 工数感

~50-100 行 (D-1 ~50 + D-2 ~30 + verify ~0)。0.5 session。proof-log `no`。

### 失敗時 fallback

- **D-1 sandwich で hypothesis 引数の shape が Phase B/C の引数と非整合**: F-2 hypothesis
  を `(P : ℝ) (hP : 0 < P) (N : ℝ≥0)` で type-cast (`P.toNNReal` vs `P : ℝ≥0`) する
  glue が散らかる可能性。Phase A 着手時に統一型を `ℝ≥0` で統一するか `ℝ` で統一するか
  確定 (judgement #5 候補)。

---

## Phase V — verify + Common2026.lean 編入準備 📋

### スコープ

3 ファイル (`AWGN.lean` / `AWGNAchievability.lean` / `AWGNConverse.lean`) の最終
verify + Common2026.lean 編入 (オーケストレータが最後にまとめて実施)。

**proof-log**: no。

### Done 条件

- `lake env lean Common2026/Shannon/AWGN.lean` clean (0 sorry, 0 warning)
- `lake env lean Common2026/Shannon/AWGNAchievability.lean` clean
- `lake env lean Common2026/Shannon/AWGNConverse.lean` clean
- `Common2026.lean` 編入位置を本 plan で指定 (オーケストレータが最後に実施)

### Common2026.lean 編入位置指定

`Common2026.lean` の既存 `import` chain で AWGN の位置を以下に挿入:

```lean
-- 既存:
import Common2026.Shannon.BlockwiseChannel
import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.ChannelCodingAchievability
import Common2026.Shannon.ChannelCodingConverseGeneralComplete
import Common2026.Shannon.ChannelCodingShannonTheoremFullDischarge
import Common2026.Shannon.DifferentialEntropy
import Common2026.Shannon.FisherInfo
-- ...

-- 新規追加 (T2-A AWGN、3 ファイル順序):
import Common2026.Shannon.AWGN                  -- Phase A + D
import Common2026.Shannon.AWGNAchievability     -- Phase B (depends on AWGN)
import Common2026.Shannon.AWGNConverse          -- Phase C (depends on AWGN)
```

**オーケストレータが最後にまとめて編集**。実装 agent は `Common2026.lean` を編集しない。

### ステップ

- [ ] **V-1** 3 ファイル `lake env lean` clean 確認
- [ ] **V-2** `Common2026.lean` 編入 (オーケストレータが実施)
- [ ] **V-3** `lake env lean Common2026.lean` clean 確認 (library root)

### 工数感

~5-10 行 (Common2026.lean に 3 行 import 追加 + verify)。0.25 session。

---

## 撤退ライン

### Scope 縮小ライン (発動時に T2-A 完成形を縮小して publish)

inventory §F の 3 ライン (F-1, F-2, F-3) を本 plan に転記:

- **F-1**: **continuous achievability の sphere packing / joint typicality を `h_typicality`
  hypothesis に外出し** (`AWGNAchievability.lean` Phase B)
  - 発動条件: T2-A 着手後 1-2 session 以内に **D.4 (continuous joint typical set +
    sphere packing) の Mathlib gap を埋められない**とき。
  - 縮退後: `awgn_achievability` の signature に `h_typicality : IsAwgnTypicalityHypothesis
    P N` を仮定として追加 (本 plan 推奨)。**Cover-Thomas 9.2 の sphere packing / continuous
    AEP machinery (球殻 volume formula、Gaussian random codebook、3 つの AEP bounds) は
    別 plan (`awgn-achievability-typicality-plan.md`) に切り出し**。本 plan の `awgn_achievability`
    は statement 完成形を publish しつつ、connectivity-typicality lemma だけ defer。
    **L-S2 (Stein) / L-F1 (de Bruijn) / L-C2 (Cramér) と同型の pattern**。

- **F-2**: **`mutualInfo` の `I = h(Y) - h(Y|X)` bridge を `h_mi_bridge` hypothesis に外出し**
  (`AWGN.lean` Phase A、判断ログ #1)
  - 発動条件: D.3 の I(X;Y) closed form 補題を直接書こうとして `klDiv_compProd_eq_add`
    連鎖から離れず、bridge 補題が 200 行を超えるとき。
  - 縮退後: `awgnCapacity_eq` / `mutualInfoOfChannel_gaussianInput_closed_form` の
    signature に `h_mi_bridge` 仮定として追加 (本 plan 推奨)。これも textbook-equivalent 形
    は publish しつつ、`h_bridge` は別 plan (`awgn-mi-bridge-plan.md`) に切り出し。
    **CLAUDE.md "Mathlib-shape-driven Definitions" のレッドフラグ「`f (compProd ...)` を
    `∫⁻ ... ∂` に直す bridge」を回避するための撤退**。

- **F-3**: **converse の per-letter max-entropy 統合形** (`AWGNConverse.lean` Phase C)
  - 発動条件: T2-A converse の `differentialEntropy_le_gaussian_of_variance_le`
    4-hypothesis を per-letter `Y_i` の law で discharge できないとき
    (`h_ent_int : Integrable (negMulLog (rnDeriv ...))` が個別 input 分布で出ない)。
  - 縮退後: `h_per_letter_aux : IsAwgnConverseIntegrableHyp P N` を converse 全体の追加
    hypothesis として外出し (本 plan 推奨)。`fano_inequality_measure_theoretic` を呼んだ
    あと max-entropy bound を `≤ h_max_gauss` で表現し直す。

**本 plan は F-1 + F-2 + F-3 の組合せ発動を想定**して計画 (seed 規模 1000-1500 行に
収めるため、判断ログ #1 で確定予定):

- F-1 採用 (Phase B): -300-500 行 (sphere packing / continuous AEP の実体を defer)
- F-2 採用 (Phase A): -200-400 行 (`mutualInfo` bridge を defer)
- F-3 採用 (Phase C): -50-100 行 (per-letter `h_ent_int` discharge を defer)
- **3 撤退ライン全採用で合計 ~550-1000 行 ship、本 plan 規模 ~1000-1300 行に収束**

### 自作 plumbing 肥大ライン (新規)

(inventory §G 危険箇所トップ 5 から本 plan に正式 import)

- **L-A1**: **`awgnChannel.measurable'` proof 規模超過** (Phase A-1 が 100 行を超える)
  - 縮退案: **`awgnChannel` の measurability proof を hypothesis form** (`h_awgn_measurable
    : Measurable (fun x => gaussianReal x N)` を引数として外出し) で publish し、
    measurability proof は別 plan (`awgn-kernel-measurability-plan.md`) に defer。
    Mathlib `Measurable.measure_of_isPiSystem_of_isProbabilityMeasure` 経由で 50-80 行
    の予想だが、超えれば即発動。

- **L-A2**: **`outputDistribution_gaussianInput` の `(p ⊗ₘ W).snd = p ∗ ν` bridge が肥大**
  (Phase A-4 が 80 行を超える)
  - 縮退案: `outputDistribution_gaussianInput` を hypothesis form で外出し、Phase B/C
    で必要に応じて discharge。Mathlib に直接 lemma がなければ `compProd_apply_prod` +
    `gaussianReal_apply` を組み合わせる ~30 行の手作業、超えれば即発動。

- **L-C1**: **Phase C chain rule per-letter の type-class 整合に詰まる**
  (`[StandardBorelSpace (Fin n → ℝ)]` `[Nonempty]` 等の自動推論が崩れる、Fano Phase 3
  経験での同様の事故)
  - 縮退案: type-class instance を local で明示的に提供 (`haveI : Nonempty (Fin n → ℝ)
    := ⟨0⟩` 等)、judgement log で記録。最大 +30 行で吸収可能、超えれば
    `awgn_converse` の statement を 1-letter form (`n = 1`) に縮退する option (但し
    Cover-Thomas 9.1.2 の完成形を犠牲)。

- **L-D1**: **3 撤退ライン全採用でも 1500 行を超える**
  - 縮退案: **Phase B (achievability) を本 plan から切り出し**、`awgn-achievability-plan.md`
    として別 plan 化。本 plan は Phase A (定義 + closed-form capacity) + Phase C (converse)
    + Phase D (sandwich 形だが achievability 部分は hypothesis pass-through) の 3 Phase
    で完結。これは roadmap T2-A の **partial publish** だが、Cover-Thomas 9.1.2 (converse)
    + closed-form capacity は単独で有用 (max-entropy 主定理の応用として publish 価値あり)。

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| **`condDistrib` の `[StandardBorelSpace Ω]` (出力側) が `Fin n → ℝ` で自動推論されない** (§危険 1、Fano Phase 3 経験) | 中 (Mathlib instance 在庫確認要) | 中 (Phase C +30-50 行 + type-class plumbing) | Phase C 着手時に loogle で `StandardBorelSpace (Fin n → ℝ)` の auto instance を確認、無ければ `instance : StandardBorelSpace (Fin n → ℝ)` を local で derive (~10-20 行)。 |
| **`Code M n α β` (`ChannelCoding.lean:151`) の decoder measurability bundle 不在** (§危険 2)、`α := ℝ` で `MeasurableSingletonClass` 偽 | **高** (確定発生) | **中** (Phase A +30-50 行) | `AwgnCode` 構造を新規定義 (Phase A-3、本 plan で確定対処)。`Code` の decoder field に measurability 追加するのではなく、AWGN 専用 wrapper として `AwgnCode` を導入し `toCode` 変換で既存 API 再利用。 |
| **`awgnChannel` measurability proof 規模超過** (§危険 3、Phase A-1 で 100 行超) | 中 (Mathlib 在庫次第) | 中 (Phase A +30-80 行 or L-A1 発動) | Mathlib `Measurable.measure_of_isPiSystem_of_isProbabilityMeasure` 経路で 50-80 行想定、超えれば L-A1 (hypothesis form) で外出し。`BlockwiseChannel.lean:77-95` の `Channel.toBlock` measurability proof schema を流用。 |
| **`differentialEntropy_le_gaussian_of_variance_le` の 4 hypothesis 中 `h_ent_int` が per-letter で discharge 不能** (§危険 4) | **高** (確定発生想定) | **中** (Phase C +0 行 + 撤退 F-3 発動) | **F-3 撤退ライン採用前提**で計画 (`IsAwgnConverseIntegrableHyp` hypothesis に外出し、`awgn-converse-aux-plan.md` に defer)。本 plan のスコープでは追加コスト 0。 |
| **`mutualInfo` KL 形 vs `I = h(Y) - h(Y|X)` 形の bridge 補題不在** (§危険 5、Mathlib-shape-driven レッドフラグ) | **高** (確定発生想定) | **高** (Phase A +200-400 行 or 撤退 F-2 発動) | **F-2 撤退ライン採用前提**で計画 (`h_mi_bridge` hypothesis に外出し、`awgn-mi-bridge-plan.md` に defer)。本 plan のスコープでは追加コスト 0。 |
| **continuous achievability (sphere packing / joint typicality on `ℝⁿ`) が Mathlib 完全不在** (§D.4) | **高** (確定発生想定) | **高** (Phase B +500-800 行 or 撤退 F-1 発動) | **F-1 撤退ライン採用前提**で計画 (`IsAwgnTypicalityHypothesis` hypothesis に外出し、`awgn-achievability-typicality-plan.md` に defer)。本 plan のスコープでは追加コスト 0 (Phase B ~150-200 行に圧縮)。 |
| **3 撤退ライン全採用でも本 plan が 1500 行を超える** | 低-中 | 中 (Phase 分割が必要) | L-D1 発動で Phase B を別 plan (`awgn-achievability-plan.md`) に切り出し。本 plan は Phase A + C + D の 3 Phase + hypothesis form で完結。 |
| **`outputDistribution = (μ ⊗ₘ W).snd = μ ∗ ν` の bridge が肥大** (Phase A-4 で 80 行超) | 中 | 低-中 (Phase A +30-50 行 or L-A2 発動) | L-A2 発動で `outputDistribution_gaussianInput` を hypothesis form 外出し。Mathlib の直接 lemma 在庫を Phase A 着手時に loogle 確認。 |
| **Phase C chain rule per-letter `condMutualInfo_chain_rule_X_2var` の type-class 整合崩れ** (`StandardBorelSpace (Fin n → ℝ)` 等) | 中 (Fano Phase 3 経験) | 中 (Phase C +30 行) | L-C1 発動で local instance 明示提供。Fano Phase 3 の対処 schema (judgement log) を流用。 |
| **Phase A + D が 1 session で完遂不能 (~250-350 行が 1 session で書けない)** | 中 | 中 (next session に持ち越し) | Phase A を 2 session に分割 (A-1 ~ A-5 = 1 session、A-6 ~ A-9 = 1 session)、Phase D は Phase C 完了後 0.5 session で完結。判断ログで session 分割を記録。 |

---

## オーケストレータ注記

- **実装 agent は `Common2026.lean` ルートを編集しない**。オーケストレータが最後に
  まとめて 3 行の `import` を追加 (Phase V V-2、上記 §Phase V の編入位置指定通り)。
- **実装 agent はコミットしない**。オーケストレータが Phase 単位 (Phase A 完了 / Phase B
  完了 / Phase C 完了 / Phase D + V 完了) で commit + push をまとめて実施。
- **撤退ライン F-1 + F-2 + F-3 の組合せ発動を想定**して計画している (seed 規模
  1000-1500 行に収めるため)。実装 agent が「`h_mi_bridge` を Phase A で discharge した」
  「`IsAwgnTypicalityHypothesis` を Phase B で discharge した」「`IsAwgnConverseIntegrableHyp`
  を Phase C で discharge した」と判断した場合、**本 plan の判断ログ #1 に append**
  してオーケストレータに連絡。撤退ライン不発動は規模 1500 行超過の確度を上げる。
- **Phase 単位の proof-log** (`proof-log-awgn-phaseA.md` / `proof-log-awgn-phaseB.md` /
  `proof-log-awgn-phaseC.md`) は実装 agent が Phase 完了時に `docs/shannon/` 直下に
  append。Phase D は proof-log なし (skeleton 整地のため)。
- **3 ファイル分離戦略の根拠** (判断ログ #2、本 plan §Approach):
  - LSP 診断と incremental compile が Phase 単位で軽くなる
  - 撤退ラインを Phase 単位で発動可能 (Tier 0 = AWGN.lean のみ publish、
    Tier 1 = + AWGNAchievability + AWGNConverse、Tier 2 = + Phase D wrapper)
  - `private` 補助補題が file-scoped (CLAUDE.md `Project Layout`) で混在しない
  - `awgn-mi-bridge-plan.md` / `awgn-achievability-typicality-plan.md` /
    `awgn-converse-aux-plan.md` の 3 別 plan に discharge を委ねる構造に整合

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### 後続 (2026-05-20, F-4 / 撤退ライン discharge)

6. **撤退ライン F-4 (kernel measurability) discharge 完了** → follow-up plan
   [`awgn-f1-discharge-moonshot-plan.md`](awgn-f1-discharge-moonshot-plan.md) で
   `Common2026/Shannon/AWGNF1Discharge.lean` (148 行) を publish。
   `Measurable (fun x : ℝ => gaussianReal x N)` を Mathlib `gaussianReal_map_const_add`
   (`μ = 0` で `(gaussianReal 0 N).map (x + ·) = gaussianReal x N`) + Giry monad
   `Measure.measurable_of_measurable_coe` + `measurable_measure_prodMk_left` の組合せで
   完全証明 (`isAwgnChannelMeasurable`)。`awgn_channel_coding_theorem` を `h_meas` 引数
   なし形で再 publish (`awgn_theorem_F1_discharged`)、capacity も同様
   (`awgn_capacity_closed_form_F1_discharged`)。当初予想 50-100 行を **map 補題に
   帰着させたことで実績 148 行**（うち本体補題 ~40 行、wrapper + header が残り）。
   seed プロンプト側では同じ箇所を「F-1 (kernel measurability)」と呼ぶ点に注意。

### 確定済 (2026-05-19, Phase A-D 一括実装)

1. **撤退ライン F-1 + F-2 + F-3 + F-4 の組合せ発動を確定**: 在庫 §F の 3 ライン
   (F-1 typicality / F-2 MI bridge / F-3 per-letter integrability) に加え、
   実装中に **新規 F-4 (`awgnChannel.measurable'` の `Measurable (fun x =>
   gaussianReal x N)` 直接構成)** を発見。Mathlib に `gaussianReal` の `m`
   (mean) -measurability の直接 lemma がない (loogle `Measurable (fun _ =>
   ProbabilityTheory.gaussianReal _ _)` で `Found 0`)。直接構成は
   `measurable_gaussianPDF` + Fubini で `(x, y) ↦ gaussianPDFReal x N y` の
   measurability 経由で 50-100 行見込み。本 plan のスコープ内で実装すると
   Tier 0 (Phase A) 規模が一気に膨張するため、`IsAwgnChannelMeasurable N` を
   hypothesis predicate に外出し、4 つの撤退ライン全採用で publish。discharge は
   別 plan `awgn-kernel-measurability-plan.md` (新規) に defer。

2. **3 ファイル分離戦略から 4 ファイルへ拡張**: 判断 #2 (Phase 0 §判断、3 ファイル
   分離) を実装中に再判断。`awgn_channel_coding_theorem` の sandwich wrapper は
   `awgn_achievability` (Achievability ファイル) と `awgn_converse` (Converse
   ファイル) の両方を import する必要があり、`AWGN.lean` 末尾に置くと循環依存
   (`AWGN.lean → AWGNAchievability.lean → AWGN.lean`) になる。**新規ファイル
   `AWGNMain.lean`** を導入し、主定理と closed-form corollary をここに集約。
   結果として 4 ファイル: `AWGN.lean` (275 行) / `AWGNAchievability.lean` (72 行) /
   `AWGNConverse.lean` (94 行) / `AWGNMain.lean` (107 行) = 合計 548 行。

3. **`AwgnCode` 4 field 確定**: 判断 #3 (Phase 0 §判断、encoder/decoder/
   decoder_meas/power_constraint の 4 field) をそのまま採用。encoder の
   measurability は `Fin M` finite ⇒ 自動充足、bundle 不要。

4. **規模 1090-1850 行予測 → 実績 548 行 (50% 縮小)**: 4 撤退ライン全採用で
   `IsAwgnTypicalityHypothesis` / `IsAwgnConverseHypothesis` /
   `IsAwgnChannelMeasurable` predicate に集約したことで、Achievability +
   Converse の本体実装が pass-through wrapper の 1 行 proof に圧縮。Phase A は
   `awgnCapacity_eq` の sandwich 周辺で本実装 (sSup の `le_csSup` / `csSup_le`、
   Gaussian variance + power constraint の bridge、MI closed-form の純算術) を
   行ったが、Phase B/C/D は 1 セッション内で完遂可能な範囲に収まった。

5. **`mutualInfoOfChannel_gaussianInput_closed_form` の純算術 fill**: F-2
   hypothesis `h_bridge` で `I = h(P+N) - h(N)` まで来た上で、
   `differentialEntropy_gaussianReal` を 2 回引いて `(1/2) log(2πe(P+N)) -
   (1/2) log(2πeN) = (1/2) log((P+N)/N) = (1/2) log(1 + P/N)` に圧縮。
   約 40 行で discharge (proof は AWGN.lean L119-170)。

<!-- 以下は Phase 着手時に append される予定の judgement log (現時点では未確定、
     skeleton として記載):

1. **(YYYY-MM-DD) Phase 0 着手時、撤退ライン F-1 + F-2 + F-3 の組合せ発動を確定**:
   inventory §F の 3 撤退ライン候補のうち、F-1 (continuous achievability hypothesis)
   と F-2 (`mutualInfo` bridge hypothesis) と F-3 (per-letter max-entropy hypothesis) を
   **本 plan の publish 前提**として採用。理由: F-2 不採用なら `mutualInfo` redefinition
   (option (c)) が必要で既存 publish 済 Stein / Sanov / Chernoff / Shannon main theorem
   を破壊、本 plan のスコープを超える。F-1 不採用なら sphere packing on `ℝⁿ` +
   Gaussian random codebook + continuous AEP の +500-800 行で seed 規模を逸脱。F-3
   不採用なら per-letter `Y_i` の `Integrable (negMulLog (rnDeriv ...))` 個別 discharge
   が input law `μ_i` 依存で一般 discharge 不能。3 撤退ライン discharge は別 plan
   (`awgn-mi-bridge-plan.md` / `awgn-achievability-typicality-plan.md` /
   `awgn-converse-aux-plan.md`) に defer。

2. **(YYYY-MM-DD) 3 ファイル分離戦略の採用 (`AWGN.lean` + `AWGNAchievability.lean` +
   `AWGNConverse.lean`)**: 判断 #2 (Phase 0 §判断) で確定。単一 `AWGN.lean` (~1250 行)
   と 3 ファイル分離の選択肢を比較し、3 ファイル分離を採用。理由: (1) Phase 単位の
   ship が独立 (Tier 0 = AWGN.lean のみで Common2026 編入可能)、(2) LSP 診断と
   incremental compile が Phase 単位で軽い、(3) `private` 補助補題が file-scoped
   (CLAUDE.md) で混在しない、(4) Tier 3 plan (3 別 plan) との discharge 構造に整合。

3. **(YYYY-MM-DD) `AwgnCode` 4 field 確定 (encoder / decoder / decoder_meas /
   power_constraint)**: 判断 #3 (Phase 0 §判断) で確定。encoder の measurability は
   `Fin M` finite ⇒ `Measurable encoder` 自動充足 (§危険 2、`MeasurableSpace.measurable_of_finite`)、
   bundle 不要。decoder の measurability は `(Fin n → ℝ) → Fin M` で `Fin n → ℝ` 側が
   continuous なので `MeasurableSingletonClass` で自動 discharge 不能、bundle 必須。

-->

---

## オーケストレータ向け Phase 着手順序サマリ

1. **Phase A (`AWGN.lean`)**: 1-1.5 session、~250-350 行、判断ログ #1+#2+#3 append。
   `lake env lean Common2026/Shannon/AWGN.lean` clean 確認。
2. **Phase B (`AWGNAchievability.lean`)**: 1-2 session、~150-200 行 (F-1 完全採用)。
   `lake env lean Common2026/Shannon/AWGNAchievability.lean` clean 確認。
3. **Phase C (`AWGNConverse.lean`)**: 1.5-2 session、~300-450 行 (F-3 完全採用)。
   `lake env lean Common2026/Shannon/AWGNConverse.lean` clean 確認。
4. **Phase D + V (`AWGN.lean` 末尾追記 + Common2026.lean 編入)**: 0.5-0.75 session、
   ~50-100 行。3 ファイル `lake env lean` clean + `Common2026.lean` 編入 (オーケストレータ)。

**合計**: ~5-7 session、~750-1100 行 (3 撤退ライン全採用)、roadmap T2-A 規模 1000-1500 行
の下限寄り。撤退ライン部分発動 (F-2 のみ採用、F-1 / F-3 を discharge) で ~1300-1600 行
中央寄り。
