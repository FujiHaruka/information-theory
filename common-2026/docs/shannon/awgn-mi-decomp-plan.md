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
> **Status (2026-05-28 更新)**: 段2 AWGN instance discharge は **完了** — `isContChannelMIDecompHyp_awgn`
> (`ContChannelMIDecomp.lean:459`) が壁の全正則性引数を Gaussian 事実で 0 sorry 供給し、`IsContChannelMIDecompHyp` を
> 仮定なし publish 済。残る唯一の sorry は **density-level chain rule 本体** = 共有壁 `contChannelMIDecomp_holds`
> (`AwgnWalls.lean:111`、`@residual(wall:awgn-mi-decomp)` + `@audit:ok`) の body (= Phases 1–6 の klDiv/Fubini 解析、
> ~200-300 行)。壁は正則性仮定付きの **true-but-hard** な状態 (判断ログ #4 参照: 旧 hyp 全落し偽壁を 2026-05-28 に修正)。
> **AWGN(#5) / Parallel Gaussian(#6) 両方が共有する foundational brick**。次の moonshot = この壁 body を埋めること。

## 進捗

- [ ] Phase 0 — signature / Markov 前提 / 在庫差分確認 + skeleton 📋 → [awgn-mi-decomp-inventory.md](awgn-mi-decomp-inventory.md)
- [ ] Phase 1 — `prod → compProd const` 書換 + KL → llr 積分展開 📋
- [ ] Phase 2 — rnDeriv 連鎖分解 (`(p⊗ₘW)/(p.prod q) = f_{Wx}/f_q`) 📋
- [ ] Phase 3 — Fubini + log 分解 (`∫∫ → ∫_x ∫_y`、`log(f_{Wx}/f_q) = log f_{Wx} − log f_q`) 📋
- [ ] Phase 4 — fibre 項同定 (`∫_x ∫_y log f_{Wx} dW_x dp = −∫ h(W x) dp`) 📋
- [ ] Phase 5 — **mixture 同定 (最重)** (`∫_x [∫_y log f_q dW_x] dp = ∫_y log f_q dq = −h(q)`) 📋
- [ ] Phase 6 — 結合 (`I = h(q) − ∫ h(W x) dp`) → 一般 body 補題 publish (🟢ʰ honest 仮定付き) 📋
- [ ] Phase 7 — **AWGN instance discharge** (honest 仮定 7本を Gaussian で全充足、`IsContChannelMIDecompHyp` 仮定なし publish) 📋
- [ ] Phase 8 — **rnDeriv joint-measurability discharge via measurable PDF proxy** (残 2 honest hyp `h_meas_fibre`/`h_int_fibre_joint` を Route B で除去、AWGN MI bridge 仮定なし化) 📋 → [awgn-rnderiv-measurability-inventory.md](awgn-rnderiv-measurability-inventory.md)
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

## Phase 8 — rnDeriv joint-measurability discharge via measurable PDF proxy 📋

> **Predecessor (inventory)**: [`awgn-rnderiv-measurability-inventory.md`](awgn-rnderiv-measurability-inventory.md)
> （feasibility **Route B 採用**、Mathlib gap `0 match`/`Found 0 declarations` で確定、消費側 use-site verbatim）

### スコープ / 確定した障害 (再導出禁止、確定事実)

Phase 7 完了後も `isContChannelMIDecompHyp_awgn` (`ContChannelMIDecomp.lean:421`) / `isAwgnMIDecomp_of_densitySplit`
(`:496`) には **2 本の honest hyp が残る**:

- `h_meas_fibre : Measurable (fun z : ℝ × ℝ => ((awgnChannel N h_meas) z.1).rnDeriv volume z.2)`
- `h_int_fibre_joint : Integrable (fun z => Real.log (((awgnChannel N h_meas) z.1).rnDeriv volume z.2).toReal) (p ⊗ₘ W)`

これらは `llr_compProd_prod_split` (`:171`) が消費する `h_meas_fibre : Measurable (fun z => (W z.1).rnDeriv volume z.2)`
(`:176`) に pin されている。**確定済の障害 (inventory §C/Q3, 本 Phase では再検証不要)**:

1. `(gaussianReal m N).rnDeriv volume` は PDF と **`=ᵐ[volume]` のみ** で一致 (`rnDeriv_gaussianReal`, 結論 `=ₐₛ`、Real.lean:240)、
   everywhere `=` ではない。⇒ measure-form rnDeriv `fun z => (gaussianReal z.1 N).rnDeriv volume z.2` の everywhere-joint
   `Measurable` は **構成不能** (rnDeriv は a.e.-determined)。
2. 消費側 `llr_compProd_prod_split` は (`:195-199`) `Measure.ae_compProd_of_ae_ae` を呼び、その第 1 goal `measurableSet_eq_fun`
   (両関数 everywhere `Measurable` 要求、`MeasureCompProd.lean:113` / `Constructions.lean:1015`) に `h_meas_fibre` を渡す。
   **`AEMeasurable` 緩和は不可** (Mathlib に `ae_compProd_of_ae_ae` / `measurableSet_eq_fun` の null-measurable 版なし)。
3. 一般 kernel ルート (`Kernel.rnDeriv_eq_rnDeriv_measure`) は `[IsFiniteKernel η]` 要求、`Kernel.const ℝ volume` は
   `IsSFiniteKernel` 止まり ⇒ **適用不可、s-finite 版も Mathlib 不在** ⇒ upstream-PR スケールで却下。

### Approach (Route B: measurable PDF proxy + consumer relaxation)

**戦略の shape**: 「埋まらない measure-form rnDeriv の everywhere measurability」を諦め、消費側の `measurableSet_eq_fun` には
**閉形式 PDF `g(x,y) := gaussianPDF x N y` (everywhere `Measurable`、自作 ~10 行) を渡す**ように `llr_compProd_prod_split`
の interface を組み替える。rnDeriv との a.e. 一致は `ae_compProd_of_ae_ae` の **第 2 引数 `∀ᵐ a, ∀ᵐ b` 側で per-fibre に消化**する。
これが既存 `integrable_log_rnDeriv_gaussianReal` (`:377`) が per-x で既に実証済の経路 (`gaussianReal_absolutelyContinuous` で
`=ᵐ[vol]` → `=ᵐ[gaussianReal]` 転送)。

**★結論も proxy 形に動かす (当初計画の修正、判断ログ #3)**。当初は「`llr_compProd_prod_split` の結論を rnDeriv 形のまま温存し、
proxy `g` は内部 (eq-set 構成) 専用に留め、最後に `g`↔rnDeriv を再接続する」設計だったが、**この再接続 (旧 8-7) は循環で構成不能**。
理由: 結論を rnDeriv 形に戻すには `(fun z => g z) =ᵐ[p⊗ₘW] (fun z => (W z.1).rnDeriv vol z.2)` が要り、これを per-fibre
`hg_ae` から立てる唯一の Mathlib 経路 `Measure.ae_compProd_of_ae_ae` (`MeasureCompProd.lean:113`) は第 1 goal
`MeasurableSet {z | g z = (W z.1).rnDeriv vol z.2}` を要求する。eq-set の `measurableSet_eq_fun` (`Constructions.lean:1015`)
は **両関数の everywhere `Measurable`** を要求し、片方が **まさに埋まらない measure-form rnDeriv の joint measurability**
⇒ Route B が回避したかった壁に再衝突。`NullMeasurableSet` 緩和も不可 (loogle `Found 0 declarations mentioning
NullMeasurableSet and Measure.compProd`、`nullMeasurableSet_eq_fun` は存在するが compProd-ae 側に null-measurable 受けが無い)。
従って `llr_compProd_prod_split` の **結論の fibre 項を `g`(= `gaussianPDF`/`gaussianPDFReal`) 形に変える**。

**blast radius が爆発しない理由 (本 Phase の核心判断)**: 結論を proxy 形にしても上位 `mutualInfoOfChannel_toReal_eq_diffEntropy_sub`
の body は **`h_llr_split` を `integral_congr_ae` (`:261`) でしか消費しない**。すなわち joint a.e. 等式を「積分の中」でしか使わない。
fibre 密度項を `g` 形に置けば、body の fibre 項処理 `Measure.integral_compProd … (:270)` → 内側 `∫ y … ∂(W x)` →
`integral_log_density_fibre` (`:76`) も **per-fibre `∫ y, log (g(x,y)).toReal ∂(W x) = −h(W x)`** に置換でき、これは `hg_ae x`
(per-fibre `g(x,·) =ᵐ[W x] (W x).rnDeriv vol`) で `integral_congr_ae` 一発、**joint measurability 不要**。同様に
`h_int_fibre_joint` (joint integrable) も proxy 形 `log (g z).toReal` で立てれば (a-1) brick が AEStronglyMeasurable を供給し、
per-fibre 積分性は既存 `integrable_log_gaussianPDFReal_gaussianReal` (`:358`) で出る。つまり **fibre 密度項を rnDeriv → proxy
に置換する作業は全て「積分 / per-fibre」レベルに閉じ、循環の壁 (joint a.e. の MeasurableSet) を一度も踏まない**。波及は
`mutualInfoOfChannel_toReal_eq_diffEntropy_sub` の `h_llr_split`/`h_int_fibre_joint` 2 引数の fibre 項を proxy 形に書き換える
だけ (output 項 `Lout`・KL→llr・Fubini split・output marginal 同定・結合は **全て不変**)。output 側は rnDeriv 形のまま温存できる
(output marginal は per-x 非依存で joint measurability 問題が無いため)。

**(a-1) 自作 brick `measurable_gaussianPDF_uncurry`** (namespace `AWGN`、`integrable_sq_sub_gaussianReal` 群の近傍に置く):

```lean
/-- 2-variable (joint) measurability of the ENNReal Gaussian pdf (Route B linchpin). -/
theorem measurable_gaussianPDF_uncurry (N : ℝ≥0) :
    Measurable (fun z : ℝ × ℝ => gaussianPDF z.1 N z.2)
```

ℝ版 `measurable_gaussianPDFReal_uncurry` も同時に出すが、**消費側が要求するのは ℝ≥0∞ 版**: 現 proof は
`(h_meas_fibre.ennreal_toReal.log)` (`:198`) で `Measurable (rnDeriv ...)` (ℝ≥0∞-valued) を受けて `.ennreal_toReal.log` を
かけている。proxy も同じ `ℝ≥0∞ → toReal → log` チェーンに乗せたいので **`g : ℝ × ℝ → ℝ≥0∞`** を eq-set 構成 (8-5) の主役にする。
**ℝ版 `measurable_gaussianPDFReal_uncurry` は 8-9 (proxy 形 joint integrable の AEStronglyMeasurable 供給) で実使用**するので
補助ではなく必須 brick。
証明: `gaussianPDF` 定義 `= ENNReal.ofReal ∘ gaussianPDFReal`、`gaussianPDFReal` 定義 (`Real.lean:48`)
`(√(2πN))⁻¹ * rexp(−(y−x)²/(2N))` を `measurable_fst`/`measurable_snd` 合成 + `Measurable.exp` + `ENNReal.measurable_ofReal`。
`√(2πN)` は定数 (N 固定)。`fun_prop` 一発で落ちる見込み (落ちなければ手動 `const_mul`/`.sub`/`.pow`/`.exp` 合成)。

**(a-2) `llr_compProd_prod_split` の interface 緩和 + 結論 proxy 化** (汎用緩和案 = inventory §自作 2(b))。
現 signature (`:171-180`) の `h_meas_fibre` 引数を **measurable proxy 三点組**に差し替え、**結論の fibre 項も `g` 形に変える**:

```lean
theorem llr_compProd_prod_split
    (q : Measure ℝ) [IsProbabilityMeasure q]
    (hWx_q : ∀ x, W x ≪ q) (hq_vol : q ≪ volume)
    (h_joint_ac : (p ⊗ₘ W) ≪ p.prod q)
    -- ↓ 旧: (h_meas_fibre : Measurable (fun z => (W z.1).rnDeriv volume z.2))
    (g : ℝ × ℝ → ℝ≥0∞) (hg_meas : Measurable g)
    (hg_ae : ∀ x, (fun y => (W x).rnDeriv volume y) =ᵐ[W x] fun y => g (x, y)) :
    (fun z => llr (p ⊗ₘ W) (p.prod q) z)
      =ᵐ[p ⊗ₘ W]
    (fun z => Real.log (g z).toReal                       -- ★ proxy 形 (旧: (W z.1).rnDeriv vol z.2)
                - Real.log (q.rnDeriv volume z.2).toReal) -- output 項は rnDeriv 形のまま温存
```

**fibre 項を proxy `g` 形に、output 項を rnDeriv 形のまま** にするのが正しい着地。理由: 旧計画の「結論を rnDeriv 形温存し
最後に `g`↔rnDeriv 再接続」は **循環で不可能** (Approach 冒頭 ★ 参照: 再接続には joint a.e. `g =ᵐ[p⊗ₘW] rnDeriv` が要り、
`ae_compProd_of_ae_ae` の `MeasurableSet` goal が埋まらない rnDeriv joint measurability に戻る)。**proxy 形に結論を変えても
blast radius は contain される**: 上位 body は `h_llr_split` を `integral_congr_ae` でしか消費しないため、fibre 項の置換は
積分レベルに閉じる (Approach 冒頭 ★ 参照)。output 項は per-x 非依存で joint measurability 問題が無いので rnDeriv 形温存でよい。

proof 内部の改修 (現 `h_split` block `:192-209`、循環を踏まない素直な構成):
- `h_split` の eq-set を **proxy `g` で直接立てる** (rnDeriv 形を経由しない)。`measurableSet_eq_fun` の第 1 関数は
  `Kernel.measurable_rnDeriv` (`:197`) 既存、第 2 関数を `(hg_meas.ennreal_toReal.log).sub
  (((Measure.measurable_rnDeriv q vol).comp measurable_snd).ennreal_toReal.log)` (proxy `g` で everywhere `Measurable`、`:198-199`)。
- `ae_compProd_of_ae_ae` の第 2 引数 (`:200-209`) に `hg_ae a` を追加 `filter_upwards`。既存 `hker` (`:203-207`, kernel
  rnDeriv → measure rnDeriv `(W a).rnDeriv q`) + `log_rnDeriv_split (hWx_q a) hq_vol` で `log (W a).rnDeriv q b
  = log (W a).rnDeriv vol b − log (q).rnDeriv vol b` を出し、そこに `hg_ae a` (`(W a).rnDeriv vol =ᵐ[W a] g(a,·)`) を貼って
  RHS の fibre 項を `log (g(a,b)).toReal` に **per-fibre で**書き換える。joint a.e. の MeasurableSet を一度も踏まない
  (per-fibre `=ᵐ[W a]` だけ使う)。

**(b) `h_int_fibre_joint` の discharge** (inventory §D/Q5): proxy 同定後、被積分関数を `log (g (z.1, z.2)).toReal` =
`log (gaussianPDFReal z.1 N z.2)` (everywhere、`toReal_gaussianPDF`) に書換え、per-fibre integrable
`integrable_log_gaussianPDFReal_gaussianReal` (`:358`) + `Measure.integral_compProd`/`integrable_compProd_iff`
(`IntegralCompProd.lean:466`) で joint に持ち上げる。joint measurability は (a-1) の proxy で供給。
per-fibre bound は log PDF = c₀ + c₁(y−x)² (`integrable_sq_sub_gaussianReal` `:341`)。**この joint integrable も結論 proxy 化に
合わせて proxy 形 `log (g z).toReal` のまま body へ渡す** (rnDeriv 形への 8-9 橋渡しは不要になる、下記参照)。

**(c) 上位 body `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` (`:223`) の fibre 項 proxy 化** (★blast radius の本体)。
旧計画は「body 不変」と書いていたが **誤り**。body の以下を proxy 形に書き換える:
- `h_llr_split` 引数 (`:228-232`) の fibre 項 `Real.log ((W z.1).rnDeriv vol z.2).toReal` → `Real.log (g z).toReal`。
  output 項は据え置き。
- `h_int_fibre_joint` 引数 (`:234-235`) の被積分関数を `Real.log (g z).toReal` に。
- proof 内 `Lfib` (`:249`) を `fun z => Real.log (g z).toReal` に、fibre 項処理 `h_fib` (`:268-277`) の内側
  `integral_log_density_fibre` (`:76`、rnDeriv 形限定) を **proxy 形の per-fibre 補題** `integral_log_proxy_fibre`
  (新規、`∫ y, log (g(x,y)).toReal ∂(W x) = −h(W x)`、`hg_ae x` + 既存 `integral_log_density_fibre` を `integral_congr_ae` で接続)
  に差し替え。**この per-fibre 補題が proxy↔rnDeriv の橋を「積分の中」で吸収し、joint measurability を回避する**。
- KL→llr (`:251-257`)、`h_split` (`:259-262`)、`h_sub` (`:264-266`)、output 項 `h_out` (`:279-307`)、結合 (`:309-310`) は **全て不変**
  (output 項は rnDeriv 形のまま、fibre 項の `g` 化と独立)。

body には新引数 `g : ℝ×ℝ → ℝ≥0∞` / `hg_meas` / `hg_ae` が増える (fibre 項を proxy 形にするため)。**output 側引数
(`hq_ac`/`h_int_out_joint`/`h_int_out_marg`) は不変**。

### Phase 詳細 (FINE-GRAINED、各 step = 1 lemma/edit、独立 `lake env lean` 可)

- [ ] **8-1 在庫差分 verify** — `gaussianPDF`/`gaussianPDFReal` の def shape (`Real.lean:48/157`) と `awgnChannel_apply`
  (`AWGN.lean:78`, `= gaussianReal x N`, `@[simp]`) を Read 再確認。`measurable_gaussianPDF_uncurry` を `fun_prop` で出せるか、
  `gaussianPDF` def を unfold して `measurable_fst`/`measurable_snd` 合成が要るかだけ確認 (loogle 1-2 query)。**how**: 調査のみ、edit なし。
- [ ] **8-2 brick `measurable_gaussianPDF_uncurry`** — file `ContChannelMIDecomp.lean` namespace `…AWGN`、
  `integrable_sq_sub_gaussianReal` (`:341`) の直前/直後。target: `Measurable (fun z : ℝ × ℝ => gaussianPDF z.1 N z.2)`。
  **how**: `unfold gaussianPDF gaussianPDFReal` → `fun_prop` (or `Measurable.const_mul (((measurable_fst.sub measurable_snd).pow _).neg.div_const _).exp |>.ennreal_ofReal`)。~10 行。
- [ ] **8-3 brick ℝ版 (補助)** — `measurable_gaussianPDFReal_uncurry : Measurable (fun z => gaussianPDFReal z.1 N z.2)`。
  **how**: 8-2 から `gaussianPDF = ofReal ∘ gaussianPDFReal` 経由、または同合成。residual #2 の `toReal` 書換で使用。~5 行。
- [ ] **8-4 `llr_compProd_prod_split` signature 緩和 + 結論 proxy 化** — target: `:171-180`。引数 `h_meas_fibre` を
  `g`/`hg_meas`/`hg_ae` 三点組に差替え、**結論の fibre 項 `Real.log ((W z.1).rnDeriv vol z.2).toReal` を `Real.log (g z).toReal`
  に変更** (output 項 `Real.log (q.rnDeriv vol z.2).toReal` は据え置き、上記 (a-2) signature 参照)。**how**: signature だけ差替え、
  proof body を `:= by sorry` に一時退避し `lake env lean` で statement が通る (型クラス OK) ことを確認。
- [ ] **8-5 eq-set を proxy `g` で直接構成 (循環を踏まない)** — `llr_compProd_prod_split` proof 内 `h_split` (`:192-209`) を改修。
  eq-set の RHS を **proxy `g` 形** (`fun z => log (g z).toReal − log (q.rnDeriv vol z.2).toReal`) で立て、`measurableSet_eq_fun`
  には第 1 関数 `(Kernel.measurable_rnDeriv W (const ℝ q)).ennreal_toReal.log` (`:197` 既存)、第 2 関数
  `(hg_meas.ennreal_toReal.log).sub (((Measure.measurable_rnDeriv q vol).comp measurable_snd).ennreal_toReal.log)` を渡す。
  **how**: `:198` の `h_meas_fibre` を `hg_meas` に置換、`h_split` の RHS (`:193-194`) を `g` 形に書換え。
- [ ] **8-6 per-fibre a.e. を `hg_ae` で消化 (joint MeasurableSet を踏まない)** — `h_split` の `ae_compProd_of_ae_ae` 第 2 引数
  (`:200-209`) に `hg_ae a` を追加 `filter_upwards`。既存 `hker` (`:203-207`) + `log_rnDeriv_split (hWx_q a) hq_vol` (`:208`) で
  `log (W a).rnDeriv q b = log (W a).rnDeriv vol b − log (q).rnDeriv vol b` を出し、`hg_ae a` (`(W a).rnDeriv vol =ᵐ[W a] g(a,·)`)
  で fibre 項を `log (g(a,b)).toReal` に **per-fibre `=ᵐ[W a]`** で置換。最後 `h_llr_eq.trans h_split` (`:217`) で 0 sorry close
  (旧 8-7 の rnDeriv 再接続は **削除**、循環ゆえ不要)。**how**: `filter_upwards [hker, log_rnDeriv_split …, hg_ae a]`、`rw [hb, hb_split, hg_b]`。
- [ ] **8-7 body fibre 項を proxy 形に書換え (★blast radius 本体、旧「body 不変」を撤回)** — target
  `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` (`:223`)。新引数 `(g : ℝ×ℝ → ℝ≥0∞) (hg_meas) (hg_ae)` を追加し、`h_llr_split`
  (`:228-232`) と `h_int_fibre_joint` (`:234-235`) の fibre 項を `Real.log (g z).toReal` に、proof 内 `Lfib` (`:249`) を
  `fun z => Real.log (g z).toReal` に。**how**: signature + `Lfib` set の書換え。output 引数・proof の他 step (KL/split/sub/out/結合) は不変。
- [ ] **8-8 proxy 形の per-fibre 補題 `integral_log_proxy_fibre`** — 新規 (namespace `ChannelCoding`、`integral_log_density_fibre`
  `:76` 近傍): target `∫ y, Real.log (g (x,y)).toReal ∂(W x) = −differentialEntropy (W x)`、前提 `W x ≪ vol` +
  `(W x).rnDeriv vol =ᵐ[W x] fun y => g (x,y)`。**how**: `integral_congr_ae` で `log (g(x,y)).toReal =ᵐ[W x] log ((W x).rnDeriv vol y).toReal`
  (`hg_ae x` から) → 既存 `integral_log_density_fibre x hWx` (`:76`) に帰着。body の `h_fib` (`:268-277`) の `integral_log_density_fibre`
  をこれに差し替え。**この補題が proxy↔rnDeriv の橋を「積分の中」で吸収する (joint measurability 不要)**。
- [ ] **8-9 `h_int_fibre_joint` discharge — proxy 形 joint integrable** — 新 lemma `integrable_log_proxy_fibre_compProd`
  (namespace `AWGN`): target `Integrable (fun z => Real.log (gaussianPDFReal z.1 N z.2)) (p ⊗ₘ W)`。
  **how**: `Measure.integrable_compProd_iff` (`:466`) で per-fibre `integrable_log_gaussianPDFReal_gaussianReal z.1 hN z.1 N` (`:358`)
  + joint AEStronglyMeasurable (8-3 の `measurable_gaussianPDFReal_uncurry`) + per-fibre bound `integrable_sq_sub_gaussianReal`。
  **rnDeriv 形への橋渡し (旧 8-9) は不要** — body が proxy 形 (8-7) を要求するので PDF 形のまま渡す。`toReal_gaussianPDF` で
  `gaussianPDFReal z.1 N z.2 = (gaussianPDF z.1 N z.2).toReal` だけ整える。
- [ ] **8-10 `isContChannelMIDecompHyp_awgn` 引数除去** — target `:421-453`。`h_meas_fibre`/`h_int_fibre_joint` 引数を削除し、
  本体で `g := fun z => gaussianPDF z.1 N z.2`、`hg_meas := measurable_gaussianPDF_uncurry N` (8-2)、`hg_ae := fun x => …`
  (per-fibre `rnDeriv_gaussianReal` + `gaussianReal_absolutelyContinuous`、`awgnChannel_apply` で `W x = gaussianReal x N`) を構成して
  `llr_compProd_prod_split` (新 signature) + body (新 signature) に渡す。`h_int_fibre_joint` は 8-9 を inline。**how**: `:452-475`
  の呼び出しを新 signature に合わせ、`g`/`hg_meas`/`hg_ae` を `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` と
  `llr_compProd_prod_split` 両方に渡す。
- [ ] **8-11 `isAwgnMIDecomp_of_densitySplit` 引数除去** — target `:496-509`。同 2 引数削除、`isContChannelMIDecompHyp_awgn`
  への pass-through (`:508-509`) から 2 引数を落とすだけ。**how**: 機械的な引数削除。
- [ ] **8-V verify** — `lake env lean Common2026/Shannon/ContChannelMIDecomp.lean` clean (0 sorry / 0 残 honest hyp)。

### Done 条件

- `isContChannelMIDecompHyp_awgn` / `isAwgnMIDecomp_of_densitySplit` が `(P,N,hN,hPN,h_meas,h_out)` のみで成立
  (`h_meas_fibre`/`h_int_fibre_joint` 引数が消滅)。AWGN MI bridge が **仮定なし**。
- `llr_compProd_prod_split` の結論は **fibre 項 proxy 形** (`Real.log (g z).toReal`)、output 項は rnDeriv 形のまま。
  これに合わせ `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` の fibre 項も proxy 形 + 新引数 `g`/`hg_meas`/`hg_ae`
  (旧計画の「body 不変」は誤りだったため撤回、判断ログ #3)。output 側 interface は不変。
- `lake env lean ContChannelMIDecomp.lean` clean、各 step 独立検証済。

### Signature が変わる定理と blast radius

| 定理 | 変更 | 波及 |
|---|---|---|
| `llr_compProd_prod_split` (`:171`) | 引数 `h_meas_fibre` → `(g)(hg_meas)(hg_ae)` 三点組。**結論の fibre 項を `Real.log (g z).toReal` (proxy 形) に変更**、output 項は rnDeriv 形のまま | 呼び出し元は `isContChannelMIDecompHyp_awgn` (`:452`) **のみ** (project 内 grep 確認済)。汎用 lemma だが現状唯一 caller |
| `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` (`:223`) | **変更 (旧「不変」を撤回)**。fibre 項を proxy 形に + 新引数 `(g)(hg_meas)(hg_ae)`。proof 内 `Lfib` (`:249`) を `log (g z).toReal` に、fibre 項処理 `h_fib` (`:268-277`) の `integral_log_density_fibre` を 8-8 の `integral_log_proxy_fibre` に差替え。**output 側引数 (`hq_ac`/`h_int_out_joint`/`h_int_out_marg`)・proof の他 step (KL/split/sub/out/結合) は不変** | 呼び出し元は `isContChannelMIDecompHyp_awgn` (`:473`) **のみ**。fibre 項置換は全て積分/per-fibre レベルに閉じ、循環 (joint a.e. の MeasurableSet) を踏まない |
| `isContChannelMIDecompHyp_awgn` (`:421`) | 引数 `h_meas_fibre`/`h_int_fibre_joint` **削除**。本体で `g`/`hg_meas`/`hg_ae` を Gaussian で構成し両 lemma に渡す | 呼び出し元 `isAwgnMIDecomp_of_densitySplit` (`:508`)。引数 2 本 drop のみ |
| `isAwgnMIDecomp_of_densitySplit` (`:496`) | 同 2 引数削除 | F-2′ wrapper。**現状 project 内に caller なし** (downstream `awgn_theorem_…`/`awgn_capacity_…` (`AWGNMIDecompBody.lean:194/221`) は `h_chain : IsContChannelMIDecompHyp` を **引数で** 取るので、`isContChannelMIDecompHyp_awgn` で埋める後継 wrapper を Phase 7/V で別途置く想定。Phase 8 はその wrapper を仮定なし化する) |

**循環の確定 (再検証済、再導出禁止)**: 旧計画の「結論 rnDeriv 形温存 + 8-7 で proxy↔rnDeriv 再接続」は **構成不能**。
proxy↔rnDeriv の joint a.e. を立てる唯一の Mathlib 経路 `Measure.ae_compProd_of_ae_ae` (`MeasureCompProd.lean:113`、第 1 引数
`MeasurableSet {x | p x}`) は、`Kernel.ae_compProd_of_ae_ae` (`CompProd.lean:257`) → `compProd_null` (`CompProd.lean:238`、
`MeasurableSet hs` 必須 + `hp.compl`) に帰着し、eq-set `{z | g z = rnDeriv z}` の measurability に `measurableSet_eq_fun`
(`Constructions.lean:1015`、両関数 everywhere `Measurable`) が要る ⇒ 埋まらない rnDeriv joint measurability に再衝突。
`NullMeasurableSet` 緩和不可 (`nullMeasurableSet_eq_fun` は `AEMeasurable.lean:197` に存在するが、compProd-ae 側に
null-measurable 受けの lemma が **無い**: loogle `Found 0 declarations mentioning NullMeasurableSet and Measure.compProd`)。
**回避策**: 結論を proxy 形にすれば再接続自体が不要になり、proxy↔rnDeriv の橋は全て per-fibre 積分 (8-6 の `=ᵐ[W a]`、
8-8 の `integral_congr_ae`) で吸収され、joint a.e. を一度も立てなくて済む。

新規追加: `measurable_gaussianPDF_uncurry` / `measurable_gaussianPDFReal_uncurry` (`AWGN` namespace) +
`integral_log_proxy_fibre` (`ChannelCoding` namespace、proxy 形 per-fibre 同定) + `integrable_log_proxy_fibre_compProd`
(`AWGN` namespace、proxy 形 joint integrable)。`Common2026.lean` の import は既存行のまま (新ファイルなし)。

### Parallel-Gaussian への波及 (本 Phase スコープ外、note のみ)

[`parallel-gaussian-chain-rule-plan.md`](parallel-gaussian-chain-rule-plan.md) は per-coord fibre density measurability
`h_meas_fibre` を AWGN #5 residual として参照している。本 Phase の brick `measurable_gaussianPDF_uncurry` +
`llr_compProd_prod_split` 緩和版は **PG が同一の per-coordinate fibre に再利用できる foundational brick**。
ただし **PG 側の channel↔RV wiring (per-coordinate compProd の組み立て) は本 Phase の対象外**。本 Phase はあくまで AWGN
single-channel の 2 honest hyp 除去まで。

### 撤退条件 / residual note

- **[D-4] consumer 緩和 (8-5〜8-8) が plumbing 超過 (>1.5 セッション)**: eq-set を `g` で直接書く `h_split` 改修 (8-5/8-6) や
  body fibre 項の proxy 化 (8-7/8-8) が `Kernel.rnDeriv` 経路と proxy 経路の a.e. 基底橋渡しで詰まる場合 → inventory §自作 2(a) の
  **特化版** `llr_compProd_prod_split_gaussian` (`W = awgnChannel`, `g = gaussianPDF` 直書き) に切替え、汎用緩和を諦める。
  特化版なら `q = gaussianReal 0 (P+N)` も具体形で `outputDistribution` の rnDeriv も PDF 同定でき、measurableSet 構成が単純化。
- **[D-5] それでも 8-5〜8-9 が closed にできない**: inventory §撤退ライン提案に従い `h_meas_fibre`/`h_int_fibre_joint` を
  **AWGN 専用 named hypothesis のまま据え置き** (= 現状維持、後退ではない)。本 Phase の brick (8-2/8-3) と緩和 skeleton のみ
  publish し、残りを follow-up に defer。
- **residual (honest が残る可能性)**: `h_int_fibre_joint` の joint integrability (8-9) で `integrable_compProd_iff` の
  AEStronglyMeasurable 前提が proxy で供給しきれない場合のみ #2 が honest に残るが、(a-1) brick (ℝ版 8-3) がそれを供給する設計なので
  中央予測では **両 hyp とも除去**。**いずれの撤退でも `sorry` は残さない** (named hypothesis signature で抜ける)。

**proof-log**: yes (`proof-log-awgn-mi-decomp-phase8.md`。結論 proxy 化の確定 (8-4)、body fibre 項 proxy 化の blast radius 実測
(8-7)、`integral_log_proxy_fibre` (8-8) で joint measurability を回避できたか、両 hyp 除去の成否、D-4/D-5 発動有無を記録)

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

1. **Phase 7 の `(W x).rnDeriv vol = gaussianPDFReal x N` 同定が楽観的すぎた (inventory `awgn-rnderiv-measurability-inventory.md`
   による修正)**: 当初 Approach §honest 仮定 AWGN discharge 表は `rnDeriv_gaussianReal` で fibre rnDeriv を PDF に
   **everywhere 同定**できる前提だったが、`rnDeriv_gaussianReal` の結論は **`=ᵐ[volume]` (=ₐₛ) のみ** で everywhere `=` ではない。
   結果 Phase 7 完了後も `h_meas_fibre` (measure-form rnDeriv の everywhere-joint `Measurable`) / `h_int_fibre_joint` が
   **2 本 honest hyp として残った** (現状の `isContChannelMIDecompHyp_awgn` `:425-430`)。measure-form rnDeriv は a.e.-determined ゆえ
   everywhere-joint `Measurable` を直接作れず、消費側 `llr_compProd_prod_split` (`:195` `ae_compProd_of_ae_ae` →
   `measurableSet_eq_fun`) は everywhere `Measurable` を要求するため `AEMeasurable` 緩和も不可。一般 kernel ルート
   (`Kernel.rnDeriv_eq_rnDeriv_measure`) は `[IsFiniteKernel η]` 要求で `Kernel.const ℝ volume` (SFinite 止まり) に不適用、
   s-finite 版も Mathlib 不在 ⇒ upstream-PR スケールで却下。
2. **Phase 8 を Route B (measurable PDF proxy + consumer relaxation) で新設**: #1 の残 2 hyp を除去する追加 Phase を立てた。
   measure-form rnDeriv の everywhere measurability は諦め、消費側の eq-set 構成には閉形式 PDF `g(x,y) := gaussianPDF x N y`
   (everywhere `Measurable`、自作 ~10 行) を渡し、rnDeriv との a.e. 一致は `ae_compProd_of_ae_ae` の per-fibre 側で消化する。
   `llr_compProd_prod_split` の **結論は rnDeriv 形のまま温存** (上位 `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` の
   interface を不変に保ち blast radius を contain)。proxy は eq-set 構成専用。撤退は D-4 (特化版へ縮退) / D-5 (現状維持) で安全。
3. **#2 の「結論 rnDeriv 形温存 + 旧 8-7 で proxy↔rnDeriv 再接続」は循環で構成不能と判明 → 結論を proxy 形に変更 (soundness fix)**:
   結論を rnDeriv 形に戻すには joint a.e. `(fun z => g z) =ᵐ[p⊗ₘW] (fun z => (W z.1).rnDeriv vol z.2)` が必要。これを per-fibre
   `hg_ae` から立てる唯一の Mathlib 経路 `Measure.ae_compProd_of_ae_ae` (`MeasureCompProd.lean:113`) は第 1 引数に
   `MeasurableSet {z | g z = (W z.1).rnDeriv vol z.2}` を要求し、その `measurableSet_eq_fun` (`Constructions.lean:1015`) は
   **両関数の everywhere `Measurable`** を要求 ⇒ 埋まらない measure-form rnDeriv の joint measurability (= Route B が回避すべき #1 の壁)
   に再衝突。`NullMeasurableSet` 緩和も不可 (`nullMeasurableSet_eq_fun` は `AEMeasurable.lean:197` にあるが compProd-ae 側に
   null-measurable 受けが無い: loogle `Found 0 declarations mentioning NullMeasurableSet and Measure.compProd`)。
   **修正**: `llr_compProd_prod_split` の結論の fibre 項を `Real.log (g z).toReal` (proxy 形) に変え、再接続 (旧 8-7) を削除。
   blast radius は **`mutualInfoOfChannel_toReal_eq_diffEntropy_sub` まで伸びる** (#2 の「body 不変」を撤回): body の fibre 項
   (`h_llr_split`/`h_int_fibre_joint`/`Lfib`) を proxy 形にし、新引数 `g`/`hg_meas`/`hg_ae` を追加。ただし body は `h_llr_split` を
   `integral_congr_ae` でしか消費せず、fibre 項処理も `Measure.integral_compProd` → 内側 per-fibre 積分なので、proxy↔rnDeriv の橋は
   全て **per-fibre 積分 (新補題 `integral_log_proxy_fibre`) で「積分の中」に吸収**でき、joint a.e. の MeasurableSet を一度も踏まない。
   output 項 (KL/split/sub/output marginal/結合) は rnDeriv 形のまま **不変**。Route B は依然 viable (中央予測 ~120-180 行)。
4. **(2026-05-28) 「shared wall への consolidate」が hyp 全落しで壁を偽にした defect → 正則性仮定を引数に復帰して修正**:
   commit `9ccbb67` が density chain-rule 壁を `AwgnWalls.contChannelMIDecomp_holds` に集約した際、**正則性仮定 #1–#6 を壁の引数から全て落とし**、`(p)[IsProbabilityMeasure p] (W)[IsMarkovKernel W]` のみで chain rule を主張する形にした。これは **普遍的に偽** (独立監査 `c40d057` 確定): 決定論チャネル `W x = dirac x` で LHS `= toReal(mutualInfoOfChannel) = toReal(⊤) = 0`、RHS `= differentialEntropy(gaussian) − 0 > 0` (`differentialEntropy_dirac = 0`、対角測度が積に特異で klDiv `= ⊤`)。落とした仮定は消費側 `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` にアンダースコア (未使用) で取り残されていた (= laundering 寄り)。
   **修正 (commit `c4388e0`、再監査 clean)**: 壁に正則性仮定を**引数として復帰**。shape は 判断ログ #2–#3 の Route B proxy 形に統一 — #1–#3 absolute continuity (plan 形) + `hWx_q : ∀ x, W x ≪ outputDistribution p W` + proxy `(g : ℝ×ℝ→ℝ≥0∞)`/`hg_meas`/`hg_ae` + joint log-integrability 2 本 (`h_int_fibre : Integrable (log (g z).toReal) (p⊗ₘW)`、`h_int_out : Integrable (log (q.rnDeriv vol z.2).toReal) (p⊗ₘW)`)。plan §段1 body (L48-66) の教科書形 (`llr`-integrable + `f·log f`-on-volume) は **不採用** — proxy 形の方が instance `isContChannelMIDecompHyp_awgn` が genuine に供給でき、`llr`-integrable は `h_int_fibre.sub h_int_out` の congr で導けるため同等以上。AWGN instance は 9 引数すべてを Gaussian 事実で **0 new sorry** discharge。壁 body は依然 `sorry` + `@residual(wall:awgn-mi-decomp)` + `@audit:ok` (signature honesty を独立確認、残る sorry = density-level chain rule の genuine Mathlib 壁 = Phases 1–6)。
   **教訓**: shared sorry 補題化のとき hypotheses を壁から落とすと over-general 化して偽になりうる。consolidate 時は regularity 前提を壁側に残すこと (memory 候補)。
