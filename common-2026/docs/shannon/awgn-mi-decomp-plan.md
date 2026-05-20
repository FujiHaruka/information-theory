# 連続チャネル MI 分解 bridge discharge ムーンショット計画 🌙 (T2-A follow-up)

<!--
雛形メモ (moonshot-plan-template.md より):
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 削除/廃止された Phase は ~~取り消し線~~ で残す（完全削除しない、過去参照のため）
- 判断ログは append-only。Phase 中の方針変更・撤退・当初仮定の修正を記録
- `rg "^- \[ \]"` で残タスク横断 grep、`rg "🔄"` でピボット箇所だけ拾える
-->

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) §撤退ライン **F-2** (MI bridge hypothesis 外出し)
>
> **Predecessor (inventory)**: [`awgn-mi-decomp-inventory.md`](awgn-mi-decomp-inventory.md)（実現可能性 **CONDITIONAL-YES**、補題 file:line + signature + 型クラス前提 verbatim）
>
> **接続点 (現状, honest pass-through)**: `Common2026/Shannon/AWGNMIBridgeDischarge.lean` 経由で読み込まれる
> `Common2026/Shannon/AWGNMIDecompBody.lean`。`IsContChannelMIDecompHyp p W` (`:144`) が AWGN 非依存の named hypothesis、
> `awgn_midecomp_of_cont_chain` (`:160`) が AWGN instance への接続子（`exact` で `IsAwgnMIDecomp` を導く）。本 plan はこの
> named hypothesis の **body を genuine に証明** し、AWGN instance では Gaussian density 事実で全仮定を discharge する。
>
> **Status (2026-05-21)**: 着手前。`AWGNMIDecompBody.lean` は F-2 を **`IsContChannelMIDecompHyp` (AWGN 非依存版) named hypothesis**
> に縮減した honest pass-through で 0 sorry 完了済。本 plan はその hypothesis を density-level klDiv 展開で discharge し、
> AWGN converse/capacity チェーンから F-2 を 1 段 unblock する。**AWGN(#5) / Parallel Gaussian(#6) 両方が共有する foundational brick**。

## 進捗

- [ ] Phase 0 — signature / Markov 前提 / 在庫差分確認 + skeleton 📋 → [awgn-mi-decomp-inventory.md](awgn-mi-decomp-inventory.md)
- [ ] Phase 1 — `prod → compProd const` 書換 + KL → llr 積分展開 📋
- [ ] Phase 2 — rnDeriv 連鎖分解 (`(p⊗ₘW)/(p.prod q) = f_{Wx}/f_q`) 📋
- [ ] Phase 3 — Fubini + log 分解 (`∫∫ → ∫_x ∫_y`、`log(f_{Wx}/f_q) = log f_{Wx} − log f_q`) 📋
- [ ] Phase 4 — fibre 項同定 (`∫_x ∫_y log f_{Wx} dW_x dp = −∫ h(W x) dp`) 📋
- [ ] Phase 5 — **mixture 同定 (最重)** (`∫_x [∫_y log f_q dW_x] dp = ∫_y log f_q dq = −h(q)`) 📋
- [ ] Phase 6 — 結合 (`I = h(q) − ∫ h(W x) dp`) → 一般 body 補題 publish (🟢ʰ honest 仮定付き) 📋
- [ ] Phase 7 — **AWGN instance discharge** (honest 仮定 7本を Gaussian で全充足、`IsContChannelMIDecompHyp` 仮定なし publish) 📋
- [ ] Phase V — verify + 親 plan F-2 退避記録の discharge 反映 📋

## ゴール / Approach

### Goal (2 段の最終定理 signature)

**段 1 — 一般 body 補題 (AWGN 非依存、honest 仮定付き、🟢ʰ)**。新規ファイル
`Common2026/Shannon/ContChannelMIDecomp.lean`:

```lean
namespace InformationTheory.Shannon.ChannelCoding

/-- ★段 1: 連続チャネル MI chain rule body。AWGN 非依存、honest 解析仮定付き。 -/
theorem mutualInfoOfChannel_toReal_eq_diffEntropy_sub
    {p : Measure ℝ} [IsProbabilityMeasure p]
    {W : Channel ℝ ℝ} [IsMarkovKernel W]                          -- ★落とし穴 1: def に無い Markov を補題側で要求
    (hW_ac     : ∀ x, W x ≪ volume)                              -- honest #1
    (hq_ac     : outputDistribution p W ≪ volume)                -- honest #2
    (h_joint_ac : (p ⊗ₘ W) ≪ p.prod (outputDistribution p W))    -- honest #3
    (h_int_llr : Integrable (llr (p ⊗ₘ W) (p.prod (outputDistribution p W))) (p ⊗ₘ W))  -- honest #4
    (h_int_fibre : ∀ᵐ x ∂p, Integrable
        (fun y => ((W x).rnDeriv volume y).toReal
                    * Real.log ((W x).rnDeriv volume y).toReal) volume)            -- honest #5
    (h_int_out : Integrable
        (fun y => ((outputDistribution p W).rnDeriv volume y).toReal
                    * Real.log ((outputDistribution p W).rnDeriv volume y).toReal) volume) :  -- honest #6
    (mutualInfoOfChannel p W).toReal
      = Common2026.Shannon.differentialEntropy (outputDistribution p W)
        - (∫ x, Common2026.Shannon.differentialEntropy (W x) ∂p) := by
  sorry  -- Phase 1-6
```

**段 2 — AWGN instance discharge (仮定なし publish)**。`ContChannelMIDecomp.lean` 末尾
（または `AWGNMIDecompBody.lean` 側からの呼び出し）で、段 1 の body へ AWGN を代入し
honest 仮定 #1–#6 + Markov を Gaussian 事実で全充足:

```lean
/-- ★段 2: AWGN instance での `IsContChannelMIDecompHyp` を仮定なしで publish。 -/
theorem isContChannelMIDecompHyp_awgn
    (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0) (hPN : P.toNNReal + N ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_out : IsAwgnOutputGaussian P N h_meas) :   -- ← 既に discharge 済 (AWGNMIBridgeDischarge)
    IsContChannelMIDecompHyp
      (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas) := by
  sorry  -- Phase 7: 段 1 を gaussianReal/awgnChannel に適用、honest #1-6 を Gaussian で discharge
```

`isContChannelMIDecompHyp_awgn` が出れば、`AWGNMIDecompBody.awgn_theorem_of_typicality_converse_midecomp_discharged`
(`:194`) / `awgn_capacity_closed_form_of_maxent_midecomp_discharged` (`:221`) の `h_chain :
IsContChannelMIDecompHyp …` 引数を **これで埋められる** ⇒ AWGN converse/capacity から F-2 が消える。
Parallel Gaussian(#6) も同じ段 1 body を per-coordinate fibre に適用して再利用できる。

### Approach (overall strategy / shape of solution)

**戦略の shape**: MI chain rule `I = h(Y) − h(Y|X)` は AWGN 固有ではなく、任意の Markov channel `W` と入力 law `p`
の **density-level 恒等式**。`mutualInfoOfChannel = klDiv (p⊗ₘW) (p.prod q)` を KL → llr 積分に開き、
joint/output/fibre の rnDeriv を Bayes 連鎖律で density 比に砕き、Fubini で 2 本の differential-entropy 積分に組み替える。
**核心インフラ (KL展開・compProd rnDeriv 連鎖律・Fubini・`prod=compProd const`・`differentialEntropy_eq_integral_density`)
は density-level で Mathlib に 100% 既存** (inventory §A–§G)。真の自作は「llr 積分 → 2 本の density 積分」への組み替え 1 本。

確定した 7 ステップ道筋 (inventory §証明戦略、これを各 Phase に割り付け):

```
┌──────────────────────────────────────────────────────────────────────────────┐
│ step 1 [Phase 1]  prod → compProd const (★最初の rewrite、必須)               │
│   mutualInfoOfChannel p W = klDiv (p⊗ₘW) (p.prod q)                          │
│     ─ Measure.compProd_const (MeasureCompProd.lean:141) ─→ klDiv (p⊗ₘW) (p ⊗ₘ const q) │
│   これを最初に置かないと compProd 連鎖律が一切発火しない (inventory 最重要 gotcha) │
│   q := outputDistribution p W                                                  │
├──────────────────────────────────────────────────────────────────────────────┤
│ step 2 [Phase 1]  KL → llr 積分                                               │
│   (klDiv (p⊗ₘW) (p.prod q)).toReal = ∫ z, llr (p⊗ₘW) (p.prod q) z ∂(p⊗ₘW)   │
│     ─ toReal_klDiv_of_measure_eq (Basic.lean:164) ─                          │
│   両者 prob measure ⇒ univ=1 一致で前提充足、integrability 不要              │
├──────────────────────────────────────────────────────────────────────────────┤
│ step 3 [Phase 2]  rnDeriv 連鎖律で density 比に分解                           │
│   (p⊗ₘW).rnDeriv (p⊗ₘ const q) (x,y) =ᵐ (W x).rnDeriv vol y / q.rnDeriv vol y │
│     ─ rnDeriv_compProd (RadonNikodym.lean:107, μ=ν=p で第1因子 1) ─          │
│     ─ Measure.rnDeriv_mul_rnDeriv (RadonNikodym.lean:402, W x≪q≪vol) ─       │
│   input density dp/dvol は約分 (μ=ν=p の rnDeriv_self=1)                      │
├──────────────────────────────────────────────────────────────────────────────┤
│ step 4 [Phase 3]  log 分解 + Fubini                                          │
│   log(f_{Wx}(y)/f_q(y)) = log f_{Wx}(y) − log f_q(y)   (Real.log_div)        │
│   ∫∫ ... ∂(p⊗ₘW) = ∫_x ∫_y [...] ∂(W x) ∂p                                  │
│     ─ Measure.integral_compProd (IntegralCompProd.lean:473, h_int_llr 消費) ─ │
├──────────────────────────────────────────────────────────────────────────────┤
│ step 5 [Phase 4]  fibre 項同定                                               │
│   ∫_x [∫_y log f_{Wx}(y) ∂(W x)] ∂p = ∫_x (−h(W x)) ∂p = −∫ h(W x) ∂p       │
│     ─ W x = vol.withDensity f_{Wx} ⇒ ∫_y g dW_x = ∫_y g·f_{Wx} dvol ─        │
│     ─ differentialEntropy_eq_integral_density (DifferentialEntropy.lean:60) ─ │
├──────────────────────────────────────────────────────────────────────────────┤
│ step 6 [Phase 5] ★最重  出力 marginal mixture 同定                          │
│   ∫_x [∫_y log f_q(y) ∂(W x)] ∂p = ∫_y log f_q(y) ∂q = −h(q)                │
│     q = outputDistribution = (p⊗ₘW).snd ⇒ ∫_x (∫_y g dW_x) dp = ∫_y g dq    │
│     (Measure.snd / integral_compProd の y-周辺化)                            │
├──────────────────────────────────────────────────────────────────────────────┤
│ step 7 [Phase 6]  結合                                                       │
│   I = −∫ h(W x) dp + h(q) = h(Y) − h(Y|X)                                    │
└──────────────────────────────────────────────────────────────────────────────┘
```

**核心 1 (Mathlib-shape-driven)**: `mutualInfoOfChannel` の右辺 `p.prod q` を **真っ先に `p ⊗ₘ const q` へ書き換える**
(step 1)。これをやらないと `rnDeriv_compProd` / `integral_compProd` のどれも形が合わず発火しない。inventory §可積分性・落とし穴で
明示された最重要 gotcha。`q` prob ⇒ `Kernel.const _ q` は Markov、`compProd_const` の `[SFinite]` 前提も prob から自動。

**核心 2 (density 砕きの三段)**: step 3 は `(W x).rnDeriv q · q.rnDeriv vol = (W x).rnDeriv vol`
(`rnDeriv_mul_rnDeriv`, vol-ae, `W x ≪ q`) で `(W x).rnDeriv q = f_{Wx}/f_q` を得る。`W x ≪ q` は honest #1 (`W x ≪ vol`)
+ honest #2 (`q ≪ vol`) + output が fibre を吸収する事実 (`absolutelyContinuous_compProd`) から導けるが plumbing が要る ⇒
AWGN instance では `gaussianReal_absolutelyContinuous` 直結で即。

**核心 3 (最重 step 6)**: 出力 entropy 項 `∫_y log f_q dq = −h(q)` を取り出す。`f_q` は `x` に依らないので Fubini の x 積分が
mixture 平均 `∫_x (∫_y g(y) ∂(W x)) ∂p` になり、これが `q = (p⊗ₘW).snd` の y 周辺積分 `∫_y g ∂q` に一致する
(`Measure.snd` の積分公式 / `integral_compProd` を g(x,y)=g(y) で潰す)。**ここが rabbit hole 化リスク最大** (mixture density
を陽に `f_q = ∫_x f_{Wx} dp` と書き下す経路は重い)。回避: g(y) が x に依らない事実だけ使い、measure-level の y 周辺化
(`Measure.snd_compProd` / `integral_snd`) で済ませる。density を陽に展開しない。

### 一般 body / AWGN instance それぞれの着地見込み

| | 着地見込み | 主リスク |
|---|---|---|
| **段 1 (一般 body)** | 🟢ʰ genuine (honest 仮定 #1–#6 + Markov 付き)。step 1–5,7 は既存 Mathlib 補題の直結で見通し良好 | **step 6 (mixture 同定)** が唯一の山場。measure-level 周辺化で逃げられれば中、density 陽展開に落ちると >100 行 |
| **段 2 (AWGN instance)** | 🟢 unconditional 見込み。honest #1–#6 は全て Gaussian 事実で discharge 可 (下表) | output Gaussian fact `IsAwgnOutputGaussian` は既に discharge 済 (`AWGNMIBridgeDischarge`)。残りは Gaussian の rnDeriv/integrability plumbing のみ |

honest 仮定の AWGN discharge 経路 (Phase 7):

| honest 仮定 | AWGN discharge | 参照 |
|---|---|---|
| #1 `∀ x, W x ≪ vol` | `awgnChannel_apply_absolutelyContinuous` | `AWGNMIDecompBody.lean:101` (済) |
| #2 `q ≪ vol` | `awgn_output_absolutelyContinuous_of_outputGaussian` | `AWGNMIDecompBody.lean:111` (済、`h_out` 必要) |
| #3 joint `≪ p.prod q` | #1 + #2 + `absolutelyContinuous_compProd` | inventory §honest #3 |
| #4 llr integrable | Gaussian llr = 2次式、`integrable_density_log_density_of_gaussian` 系で fibre 化 | `DifferentialEntropy.lean:81` |
| #5 fibre `f log f` int | `integrable_density_log_density_of_gaussian` (各 fibre `gaussianReal x N`) | `DifferentialEntropy.lean:81` |
| #6 output `f log f` int | `integrable_density_log_density_of_gaussian` (`gaussianReal 0 (P+N)`) | `DifferentialEntropy.lean:81` |
| Markov | `awgnChannel.instIsMarkovKernel` / `Kernel.const` Markov | `AWGN.lean:82` |

加えて Phase 7 では fibre/output の **density 表現** (`gaussianReal m v = vol.withDensity (ofReal ∘ gaussianPDFReal m v)`,
`gaussianReal_of_var_ne_zero`) と `rnDeriv_gaussianReal` で `(W x).rnDeriv vol = gaussianPDFReal x N` を同定し、段 1 の
honest 仮定形にはめ込む。

### 規模見積もり (中央予測)

| 自作要素 | 想定行数 | Phase |
|---|---|---|
| skeleton + imports + docstring + namespace | ~30-40 | 0 |
| step 1+2 (`compProd_const` rewrite + `toReal_klDiv_of_measure_eq` 起動 + univ 一致) | ~30-50 | 1 |
| step 3 (`rnDeriv_compProd` + `rnDeriv_mul_rnDeriv`、ae 等式の `integral_congr_ae` 接続) | ~50-80 | 2 |
| step 4 (`Real.log_div` + `integral_compProd` Fubini、negMulLog 0 境界処理) | ~40-60 | 3 |
| step 5 (fibre `differentialEntropy_eq_integral_density` 接続、withDensity 積分変換) | ~30-50 | 4 |
| **step 6 (mixture 同定、measure-level 周辺化)** | **~40-100** | 5 |
| step 7 (結合 ring + 符号合わせ) | ~15-25 | 6 |
| `isContChannelMIDecompHyp_awgn` (AWGN instance、honest #1–#6 discharge plumbing) | ~80-150 | 7 |
| **合計** | **~315-555** | |

**中央予測 ~430 行** (inventory §自作 1「150–220 行」+ AWGN discharge plumbing ~100–150 行 + 段 1 周辺の整合性)。
段 1 だけで止まれば (Phase 6 完了、Phase 7 を後続へ defer) ~250 行で一般 body は publish 価値あり。

### ファイル構成

新規 `Common2026/Shannon/ContChannelMIDecomp.lean` (inventory §着手 skeleton 準拠):

```
Common2026/Shannon/
  AWGNMIDecompBody.lean        ← 既存。IsContChannelMIDecompHyp def (:144) は不変。
                                  awgnChannel_apply_absolutelyContinuous (:101) 等 Phase A 事実を再利用
  ContChannelMIDecomp.lean     ← 新規 (~315-555 行)。段 1 body + 段 2 AWGN instance
Common2026.lean                ← import Common2026.Shannon.ContChannelMIDecomp 追記
```

`AWGNMIDecompBody.awgn_theorem_of_typicality_converse_midecomp_discharged` (`:194`) の `h_chain` 引数は、本 plan 完了後
`isContChannelMIDecompHyp_awgn` で埋める後継 wrapper を ContChannelMIDecomp.lean (または AWGNMIDecompBody 末尾) に置く。
**`IsContChannelMIDecompHyp` の def 自体は触らない** (落とし穴 1: Markov 前提が def に無いため body 補題側で要求)。

## 撤退ライン

親計画 `awgn-moonshot-plan.md` §撤退ライン **F-2**: MI bridge を hypothesis として converse 全体へ外出し。現状
`AWGNMIDecompBody.lean` は F-2 を **`IsContChannelMIDecompHyp` (AWGN 非依存版) named hypothesis** に縮減した honest
pass-through。本 plan はその hypothesis を genuine 化する。

撤退の段階 (浅い順):

- **[D-1] 段 1 のみ publish、Phase 7 defer**: Phase 6 まで完了で一般 body `mutualInfoOfChannel_toReal_eq_diffEntropy_sub`
  (honest #1–#6 付き 🟢ʰ) を publish し、AWGN instance discharge (Phase 7) を後続 plan へ defer。一般 body は単独で
  Parallel Gaussian(#6) からも import 可能な foundational brick ⇒ publish 価値あり。`IsContChannelMIDecompHyp` は named
  hypothesis のまま温存。
- **[D-2 = F-2′] step 6 (mixture 同定) が rabbit hole (>100 行)**: inventory §F-2′ に従い縮退。output を
  `q = vol.withDensity f_q` + output density 表現 / integrability を **named honest 仮定**として段 1 に残す形に body を立てる。
  それでも段 1 は genuine (mixture 同定だけ仮定化、残りの klDiv→density 構造は陽に証明)。AWGN instance は `q = gaussianReal 0 (P+N)`
  の具体形で `f_q = gaussianPDFReal 0 (P+N)` が取れる (`awgn_output_absolutelyContinuous_of_outputGaussian` + `gaussianReal_of_var_ne_zero`)
  ⇒ 段 2 は依然 unconditional 充足。**F-2′ は F-2 (MI 公式まるごと hypothesis) より 1 段階具体的**。
- **[D-3] 段 1 全体が型クラス壁 (Markov / SFinite / SigmaFinite の解決不能)**: 親 plan F-2 をそのまま温存
  (`IsContChannelMIDecompHyp` named hypothesis 据え置き)。本 plan は inventory + skeleton + 型クラス壁の正確な記録のみ publish。

**いずれの撤退でも `sorry` は残さない** (honest pass-through / 明示 hypothesis signature で抜ける。CLAUDE.md 撤退ライン規約)。

## 依存関係

完了済 / 利用可:

- [x] **Mathlib `InformationTheory.KullbackLeibler.Basic`**: `toReal_klDiv_of_measure_eq` (`:164`, 主役), `toReal_klDiv` (`:157`, fallback), `klDiv` (`:57`)
- [x] **Mathlib `MeasureTheory.Measure.LogLikelihoodRatio`**: `llr` (`:37`), `llr_def` (`:39`)
- [x] **Mathlib `Probability.Kernel.Composition.RadonNikodym`**: `rnDeriv_compProd` (`:107`, 核心), `rnDeriv_measure_compProd_left` (`:92`)
- [x] **Mathlib `MeasureTheory.Measure.Decomposition.RadonNikodym`**: `Measure.rnDeriv_mul_rnDeriv` (`:402`, 核心), `Measure.rnDeriv_mul_rnDeriv'` (`:410`), `Measure.rnDeriv_withDensity`
- [x] **Mathlib `Probability.Kernel.Composition.IntegralCompProd`**: `MeasureTheory.integral_compProd` (`:473`, 主役), `Measure.integrable_compProd_iff` (`:466`)
- [x] **Mathlib `Probability.Kernel.Composition.MeasureCompProd`**: `Measure.compProd_const` (`:141`, 主役), `Measure.snd_compProd` (mixture 周辺化、Phase 5)
- [x] **Mathlib `InformationTheory.KullbackLeibler.ChainRule`**: `integral_llr_compProd_eq_add` (`:151`, 任意), `klDiv_compProd_left` (`:182`), `klDiv_compProd_eq_add` (`:204`)
- [x] **Mathlib `Probability.Distributions.Gaussian.Real`**: `gaussianReal_absolutelyContinuous`, `gaussianReal_of_var_ne_zero` (= withDensity gaussianPDF), `rnDeriv_gaussianReal` (Phase 7)
- [x] **`Common2026/Shannon/DifferentialEntropy.lean`**: `differentialEntropy` (`:42`), `differentialEntropy_eq_integral_density` (`:60`, 主役), `differentialEntropy_eq_integral_withDensity` (`:47`), `integrable_density_log_density_of_gaussian` (`:81`, Phase 7)
- [x] **`Common2026/Shannon/ChannelCoding.lean`**: `Channel` (`:49`), `mutualInfoOfChannel` (`:84`), `outputDistribution` (`:71`), `jointDistribution` (`:54`), 各 IsProbabilityMeasure instance
- [x] **`Common2026/Shannon/AWGNMIDecompBody.lean`**: `IsContChannelMIDecompHyp` (`:144`, def 不変), `awgnChannel_apply_absolutelyContinuous` (`:101`), `awgn_output_absolutelyContinuous_of_outputGaussian` (`:111`), `awgn_midecomp_of_cont_chain` (`:160`, 接続子)
- [x] **`Common2026/Shannon/AWGN.lean`**: `awgnChannel` (`:75`), `awgnChannel_apply` (`:78`), Markov instance (`:82`)

**参考 (import しない / 不採用)**: `integral_llr_compProd_eq_add` 経由の chain rule 直呼び (§A→§D 経路で代替可、必須ではない)。

---

## Phase 0 — signature / Markov 前提 / 在庫差分確認 + skeleton 📋

### スコープ

inventory は実態として十分詳細だが、着手前に 3 点を verify:

1. **`compProd_const` の前提実体**: `Measure.compProd_const` (`MeasureCompProd.lean:141`) の `[SFinite μ] [SFinite ν]` が
   `p` / `q` (共に prob) から自動 dispatch されるか。失敗時は `Kernel.const_apply` ベースの手動書換に切替。
2. **`rnDeriv_compProd` の `μ=ν=p` 特殊化**: 第1因子 `p.rnDeriv p` が `1` に落ちる lemma (`Measure.rnDeriv_self`) の正確な ae 基底
   (`p`-ae vs `vol`-ae) と、`rnDeriv_compProd` の `=ᵐ[ν⊗ₘη]` 基底 (`ν=p` ⇒ `p ⊗ₘ const q`-ae) の整合。
3. **mixture 周辺化 lemma の存在**: step 6 で使う `∫_x (∫_y g dW_x) dp = ∫_y g dq` の measure-level 形が Mathlib に
   `Measure.snd` / `integral_snd` / `integral_compProd` (g が第1成分非依存) のどれで取れるか loogle で確定。**ここが Phase 5 撤退判断の前提**。

### 成果物

- skeleton `Common2026/Shannon/ContChannelMIDecomp.lean` (段 1 body + 段 2 instance を `:= by sorry`、全 `sorry` で type-check)
- 本計画書への反映 (Phase 5 の周辺化 lemma 確定 → Approach 核心 3 / 撤退ライン D-2 の更新)

### Done 条件

- skeleton が `lake env lean` で sorry warning のみ (型クラス前提が全て解決、`[IsMarkovKernel W]` 込みで段 1 の statement が通る)
- 上記 3 点が loogle + Read で裏取り済 (特に mixture 周辺化 lemma 名)

### 工数感

0.5 セッション。subagent 不要 (inventory 済)、ローカル `loogle` / `Read` のみ。**proof-log**: no (調査 + skeleton のみ)

---

## Phase 1 — `prod → compProd const` 書換 + KL → llr 積分展開 📋

### スコープ

step 1 + step 2。`mutualInfoOfChannel p W = klDiv (p⊗ₘW) (p.prod q)` の `p.prod q` を `compProd_const` で `p ⊗ₘ const q` に
書換 (★必須、最初に置く)、`toReal_klDiv_of_measure_eq` で `(klDiv …).toReal = ∫ z, llr (p⊗ₘW) (p.prod q) z ∂(p⊗ₘW)` を得る。

### Done 条件

- `(mutualInfoOfChannel p W).toReal = ∫ z, llr (p⊗ₘW) (p.prod q) z ∂(p⊗ₘW)` が証明済 (honest #3 `h_joint_ac` 消費、univ 一致は `measure_univ` 即)
- 後続 step 用に `p.prod q = p ⊗ₘ const q` の書換が確立 (Phase 2 の `rnDeriv_compProd` 起動準備)

### 撤退条件

- `toReal_klDiv_of_measure_eq` の univ 一致前提 `(p⊗ₘW) univ = (p.prod q) univ` が prob から即取れない場合 → `toReal_klDiv` (`:157`, 一般版) に切替 (`ν.real univ − μ.real univ = 0` を手で消す、+1 補題)

**proof-log**: yes (Phase 1 完了で `proof-log-awgn-mi-decomp-phase1.md` append)

---

## Phase 2 — rnDeriv 連鎖分解 📋

### スコープ

step 3。`(p⊗ₘW).rnDeriv (p ⊗ₘ const q) (x,y) =ᵐ (W x).rnDeriv vol y / q.rnDeriv vol y` を確立。
`rnDeriv_compProd` (μ=ν=p、第1因子を `Measure.rnDeriv_self`=1 で潰す) で fibre rnDeriv `(W x).rnDeriv q y` を取り出し、
`Measure.rnDeriv_mul_rnDeriv` (`W x ≪ q ≪ vol`) で `(W x).rnDeriv q = f_{Wx}/f_q` (vol-ae) に砕く。

### Done 条件

- `llr (p⊗ₘW) (p.prod q) (x,y) =ᵐ Real.log (((W x).rnDeriv vol y).toReal / (q.rnDeriv vol y).toReal)` が ae 等式で確立
- `W x ≪ q` を honest #1 + #2 (+ `absolutelyContinuous_compProd`) から導出 or honest 仮定として明示追加

### 撤退条件

- `rnDeriv_compProd` の ae 基底 (`p ⊗ₘ const q`-ae) と `rnDeriv_mul_rnDeriv` の ae 基底 (`vol`-ae、fibre 内) の橋渡しが
  詰まる → step 3 を「fibre ごとに `(W x).rnDeriv q =ᵐ[vol] f_{Wx}/f_q」+ Fubini 後に貼る順序へ組替 (Phase 3 と境界を移動)

**proof-log**: yes

---

## Phase 3 — Fubini + log 分解 📋

### スコープ

step 4。`Real.log_div` で `log(f_{Wx}/f_q) = log f_{Wx} − log f_q`、`Measure.integral_compProd` で
`∫ z ... ∂(p⊗ₘW) = ∫_x ∫_y [...] ∂(W x) ∂p` に Fubini 展開 (honest #4 `h_int_llr` 消費)。`negMulLog 0 = 0` /
`f_{Wx}(y)=0` 点の log 暴れは `rnDeriv = 0` 分岐を `simp` で吸収 (inventory 落とし穴 3)。

### Done 条件

- `(mutualInfoOfChannel p W).toReal = ∫_x [∫_y (log f_{Wx}(y) − log f_q(y)) ∂(W x)] ∂p` が確立
- log_div の 0-分母 / 0-分子 境界処理が完了 (ae で f>0 を確保 or negMulLog の 0 連続拡張で吸収)

### 撤退条件

- Fubini の被積分可積分性 (`h_int_llr` を fibrewise に砕く `integrable_compProd_iff`) が重い → 段 1 に fibre-integrability を
  追加 honest 仮定として持ち上げ (honest #5 を強める)

**proof-log**: yes

---

## Phase 4 — fibre 項同定 📋

### スコープ

step 5。`∫_x [∫_y log f_{Wx}(y) ∂(W x)] ∂p = −∫_x h(W x) ∂p`。各 fibre で `W x = vol.withDensity f_{Wx}` ⇒
`∫_y g ∂(W x) = ∫_y g·f_{Wx} dvol`、`differentialEntropy_eq_integral_density` で `∫_y f_{Wx} log f_{Wx} dvol = −h(W x)`。

### Done 条件

- `∫_x [∫_y log f_{Wx}(y) ∂(W x)] ∂p = −∫ x, differentialEntropy (W x) ∂p` が確立 (honest #5 消費)
- fibre density 表現 `W x = vol.withDensity (ofReal ∘ f_{Wx})` を honest #1 (`W x ≪ vol`) + `withDensity_rnDeriv_eq` で取得

### 撤退条件

- `∫_y g ∂(W x) = ∫_y g·f_{Wx} dvol` の withDensity 積分変換 (`integral_withDensity_eq_integral_smul` 系) の
  ENNReal↔Real toReal 整合が重い → fibre 項を `∫_x (∫_y negMulLog (f_{Wx} y).toReal dvol) dp` 形に直接持ち込み

**proof-log**: yes

---

## Phase 5 — mixture 同定 (★最重) 📋

### スコープ

step 6。`∫_x [∫_y log f_q(y) ∂(W x)] ∂p = ∫_y log f_q(y) ∂q = −h(q)`。`f_q` は `x` 非依存 ⇒ Fubini の x 積分は mixture
平均、これが `q = (p⊗ₘW).snd` の y 周辺積分に一致 (`Measure.snd_compProd` / `integral_snd`、g が第1成分非依存)。**measure-level
の周辺化で済ませ、mixture density `f_q = ∫_x f_{Wx} dp` を陽に展開しない** (rabbit hole 回避)。

### Done 条件

- `∫_x [∫_y log f_q(y) ∂(W x)] ∂p = differentialEntropy q` (= `−∫_y f_q log f_q dvol` の符号付き) が確立 (honest #6 消費)
- output density 表現 `q = vol.withDensity (ofReal ∘ f_q)` を honest #2 から取得、`differentialEntropy_eq_integral_density` 接続

### 撤退条件 (= 本 plan の主撤退判断点)

- **measure-level 周辺化 (`Measure.snd_compProd` 経由) で `∫_x (∫_y g dW_x) dp = ∫_y g dq` が直結しない**、かつ density 陽展開
  に落ちて >100 行 → **撤退ライン D-2 (F-2′) 発動**: output を `q = vol.withDensity f_q` + output density / integrability を
  named honest 仮定として段 1 に残す。段 1 は genuine のまま、AWGN instance は `q = gaussianReal 0 (P+N)` で具体充足。

**proof-log**: yes (Phase 5 完了 or D-2 撤退のどちらでも append、判断ログ #1 候補)

---

## Phase 6 — 結合 → 一般 body publish 📋

### スコープ

step 7。Phase 4 (`−∫ h(W x) dp`) + Phase 5 (`h(q)` 相当) を結合し `I = h(q) − ∫ h(W x) dp` = 段 1 の goal に整える
(符号合わせ + `ring` / `sub_eq_add_neg`)。段 1 補題 `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` を publish。

### Done 条件

- 段 1 補題が `lake env lean ContChannelMIDecomp.lean` で 0 sorry (honest #1–#6 + Markov 引数付き、🟢ʰ)
- `Common2026.lean` に import 追記 (段 2 未完なら段 1 のみ publish した状態で一旦)

**proof-log**: yes (一般 body 着地、判断ログ反映)

---

## Phase 7 — AWGN instance discharge 📋

### スコープ

段 2。段 1 body を `p := gaussianReal 0 P.toNNReal`, `W := awgnChannel N h_meas` に適用し、honest #1–#6 + Markov を
Gaussian 事実で全 discharge (Approach §honest 仮定 AWGN discharge 表)。`isContChannelMIDecompHyp_awgn` を **仮定なし** (P,N,h_meas,
output Gaussian fact のみ) で publish。fibre/output density は `gaussianReal_of_var_ne_zero` (withDensity gaussianPDF) +
`rnDeriv_gaussianReal` で段 1 の honest 仮定形にはめる。

### Done 条件

- `isContChannelMIDecompHyp_awgn` が 0 sorry で publish (honest #1–#6 を Gaussian で全 discharge)
- 後継 wrapper で `AWGNMIDecompBody.awgn_theorem_of_typicality_converse_midecomp_discharged` (`:194`) の `h_chain` 引数を
  `isContChannelMIDecompHyp_awgn` で埋めた discharge 形を publish (F-2 が AWGN converse/capacity から消える)

### 撤退条件

- honest #4 (joint llr integrability) の Gaussian discharge が重い (Gaussian llr=2次式の `p⊗ₘW`-integrability plumbing) →
  #4 を AWGN instance でも named hypothesis として一旦残し (段 2 を conditional に)、#1–#3,#5,#6 + Markov のみ discharge

**proof-log**: yes (AWGN instance 着地、F-2 discharge 反映)

---

## Phase V — verify + 親 plan F-2 退避記録の discharge 反映 📋

### スコープ

`lake env lean Common2026/Shannon/ContChannelMIDecomp.lean` clean 確認、`Common2026.lean` import、親 plan
`awgn-moonshot-plan.md` §撤退ライン F-2 + `AWGNMIDecompBody.lean` docstring の「F-2 named hypothesis 据え置き」記述を
discharge 状態に更新する旨を記録 (実装は lean-implementer、本 plan は反映指示のみ)。

### Done 条件

- 全 Phase の着地状態 (段 1 / 段 2 / 撤退発動有無) が進捗ブロック + 判断ログに反映
- 親 plan F-2 への discharge リンクが本 plan から張られている

**proof-log**: no (verify + 反映のみ)

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 着手後に append。Phase 5 (mixture 同定) の measure-level 周辺化 vs density 陽展開の判断、D-2 (F-2′) 発動有無、
honest 仮定の最終本数 (#1-#6 + Markov)、Phase 7 の honest #4 discharge 可否がここに記録される見込み。 -->
