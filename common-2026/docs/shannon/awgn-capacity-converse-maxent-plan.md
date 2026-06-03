# AWGN single-letter capacity converse (max-entropy 壁) closure 計画 🌙

<!--
雛形メモ (moonshot-plan-template.md より):
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 削除/廃止された Phase は ~~取り消し線~~ で残す（完全削除しない、過去参照のため）
- 判断ログは append-only。Phase 中の方針変更・撤退・当初仮定の修正を記録
- `rg "^- \[ \]"` で残タスク横断 grep、`rg "🔄"` でピボット箇所だけ拾える
-->

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) §撤退ライン **F-3** の下流 (single-letter capacity converse の Mathlib gap closure)
>
> **Predecessor (inventory)**: [`awgn-capacity-converse-maxent-inventory.md`](awgn-capacity-converse-maxent-inventory.md)
> （実現可能性 **(ii) 自作 real-analysis 補題 5〜6 本 / 200〜300 行**、API file:line + signature + 型クラス前提 verbatim、着手 skeleton 草案 L249-300）
>
> **対象壁**: `@residual(wall:awgn-capacity-converse-maxent)`
> (`docs/audit/audit-tags.md` Wall name register `:75`、`InformationTheory/Draft/Shannon/ContChannelMIDecomp.lean:692`
> `awgn_capacity_closed_form_of_out` body 内 `h_max_ent` の `sorry`)
>
> **隣接壁 (集約対象)**: `@residual(wall:awgn-per-letter-integrability)`
> (`InformationTheory/Shannon/AwgnWalls.lean:251` `awgnPerLetterIntegrability_holds`)。**同型の Mathlib gap** =
> Gaussian mixture 出力 log-density 可積分性 (`differentialEntropy_le_gaussian_of_variance_le` の `h_ent_int`,
> `DifferentialEntropy.lean:518`)。Phase 3 で 1 本の shared sorry 補題に集約候補 (条件は撤退ライン参照)。

## 進捗 — ✅ CLOSED 2026-05-29 (commit f8549b9, wall genuine closure / proof done)

> **壁 `awgn-capacity-converse-maxent` は genuine に閉じた**。`AwgnCapacityConverseMaxent.lean` 0 sorry / 0 residual、
> `#print axioms` で `sorryAx` 非依存 (標準 3 公理のみ) を独立監査が機械確認、6 declaration に `@audit:ok`。
> 最終 genuine 定理: `awgn_capacity_closed_form_genuine : awgnCapacity P N = (1/2)log(1+P/N)`。
> 前提: constraint set の false-statement defect を lintegral pivot で修正 (別途独立監査 OK)。

- [x] Phase 0 — signature / import 方向 verbatim 確認 + skeleton ✅ (import 方向 (a): 新 file が genuine closed-form publish)
- [x] Phase 1 — `gaussianPDFReal_le_sup` (#5) ✅
- [x] Phase 2 — `outputDistribution_awgn_eq_conv` (#1) ✅
- [x] Phase 3 — `capacity_log_diff` 算術 (#6) ✅
- [x] Phase 4 — `output_secondMoment_eq` / `output_variance_le` Var(Y) ≤ P+N (#2) ✅
- [x] Phase 5 — `fibre_absolutelyContinuous_output_general` (#4) ✅
- [x] Phase 6 — ★ `outputDistribution_logDensity_integrable` (#3, hard) ✅ (撤退ライン L-CONV 不発、6b まで genuine)
  - [x] 6a — Gaussian pdf 上界 → `log f_q ≤` 定数 ✅ (`outputMixtureDensity_le_sup`)
  - [x] 6b — ★ mixture 下界 `f_q(y) ≥ c·exp(−a·y²)` ✅ genuine (`output_logDensity_lower_bound`, Chebyshev + Gaussian tail)
  - [x] 6c — `|log f_q| ≤ c₀ + c₁·y²` 結合 + `Integrable.mono'` ✅ (`outputMixtureDensity_log_abs_le`)
  - [x] 6d — joint lift (`p⊗ₘW` 形 / volume 形) ✅
- [x] Phase 7 — 最終結線 `awgn_per_input_mi_le_log` + `awgn_capacity_closed_form_genuine` publish ✅
- [x] Phase V — verify + `InformationTheory.lean` import 済 + 旧 `_of_out` wrapper 削除 (superseded) + wall register CLOSED ✅

### 計画外で判明した重要事項 (実装中)
- **🔴 constraint-set false-statement defect (tier-5)**: 着手前の `awgnCapacity` constraint set は Bochner `∫x²∂p≤P` で、
  非可積分 (二次モーメント ∞) 入力が `integral_undef→0≤P` で紛れ込み converse を偽にしていた。lintegral 形
  `awgnPowerConstraintSet` に pivot して修正 (9 file 横断、別 commit、独立監査 OK)。
- **6a 密度表示**: 計画想定の `rnDeriv_conv` は一般 `p` (非 `≪volume`) で不適用 → `withDensity` 直接構成
  (`output_eq_withDensity_mixture`) に pivot。
- **whnf/heartbeat timeout**: `gaussianPDF` を絡める lintegral/Measurable で頻発。「密度を `set` で不透明化」+
  「mean パラメータ可測性を独立補題 `measurable_gaussianPDF_fst` に切出し」で回避。
- **ParallelGaussian 多次元版に同型 defect 残存** (`ParallelGaussian.lean:166`)、別ライン (後回し、handoff 参照)。

## ゴール / Approach

### Goal (最終定理 signature)

`InformationTheory/Draft/Shannon/ContChannelMIDecomp.lean:687-692` の body-`have` `h_max_ent` を、新規 file
`InformationTheory/Draft/Shannon/AwgnCapacityConverseMaxent.lean` の補題で genuine に供給する:

```lean
/-- 本壁の最終結論 (`awgn_capacity_closed_form_of_out` の `h_max_ent` を供給). -/
theorem awgn_per_input_mi_le_log
    (hP : 0 < P) (hN : (N : ℝ) ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    (p : Measure ℝ) [IsProbabilityMeasure p] (hp_2mom : ∫ x, x^2 ∂p ≤ P) :
    (ChannelCoding.mutualInfoOfChannel p (awgnChannel N h_meas)).toReal
      ≤ (1/2) * Real.log (1 + P / (N : ℝ)) := by ...
```

**unconditional signature を保つ** (`p` は任意 input、second-moment `≤ P` は regularity precondition、
load-bearing hyp 一切なし)。これを `ContChannelMIDecomp.lean:692` の `sorry` に `exact awgn_per_input_mi_le_log …`
で結線すると壁本体が closure する。

### Approach (overall strategy / shape of solution)

**一本道 = `I(X;Y) = h(Y) − h(Y|X)` 分解 → Gaussian max-entropy 上界 + 分散評価**。Cover-Thomas 9.1 converse そのもの。
別ルート (MI を直接上から押さえる DPI / variational 形) は **Mathlib 不在で不可能** (inventory §D 確定: `klDiv` の
pushforward 単調性 loogle 0 件、`mutualInfo` namespace 不在、`klDiv ≤` は下界 Pinsker のみ)。よって chain rule 経由が唯一。

主役 2 本は **in-tree で genuine 完成済 / 既存**:

- **chain rule** `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` (`ContChannelMIDecomp.lean:276`、0 sorry `@audit:ok`)
  = `I = h(q) − ∫ h(W x) dp`。**proxy 形 9 引数**を要求 (絶対連続性 3 + `hWx_q` + proxy `g`/`hg_meas`/`hg_ae` +
  joint log-integrability 2 本 `h_int_fibre`/`h_int_out`)。
- **max-entropy** `differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:520`、既存) =
  `h(q) ≤ (1/2)log(2πe·v)` (`Var(Y) ≤ v`)。`h_var_int` + `h_ent_int` を要求。

道筋 (5 step、Cover-Thomas 9.1 converse):

```
┌──────────────────────────────────────────────────────────────────────────────┐
│ step 1  MI = h(Y) − h(Y|X)  [chain rule、proxy 形 9 引数を AWGN で discharge]   │
│   q := outputDistribution p W = p ∗ 𝒩(0,N)  (Phase 2)                          │
│   絶対連続性 3 + hWx_q (Phase 5) + g := gaussianPDF (#measurable_gaussianPDF_   │
│   uncurry, in-tree :370) + h_int_fibre (in-tree integrable_log_gaussianPDFReal_│
│   gaussianReal, fibre 側) + h_int_out (★ Phase 6 本壁)                          │
├──────────────────────────────────────────────────────────────────────────────┤
│ step 2  h(Y|X) = ∫ h(𝒩(x,N)) dp = (1/2)log(2πeN)  [定数、fibre entropy]        │
│   awgnChannel_apply + differentialEntropy_gaussianReal (in-tree)               │
├──────────────────────────────────────────────────────────────────────────────┤
│ step 3  h(Y) ≤ (1/2)log(2πe·Var(Y))  [max-entropy、既存]                       │
│   m := ∫y∂q (= E[Y]、★ m:=0 は誤り)、h_mean/h_var/h_var_int (Phase 4) +        │
│   h_ent_int (★ Phase 6 本壁、h_int_out と同型)                                  │
├──────────────────────────────────────────────────────────────────────────────┤
│ step 4  Var(Y) ≤ E[X²] + N ≤ P + N  [IndepFun.variance_add + var_le_E_sq]      │
│   Phase 4                                                                      │
├──────────────────────────────────────────────────────────────────────────────┤
│ step 5  算術: (1/2)log(2πe(P+N)) − (1/2)log(2πeN) = (1/2)log(1+P/N)            │
│   Phase 3 (mutualInfoOfChannel_gaussianInput_closed_form の log 代数を流用)    │
└──────────────────────────────────────────────────────────────────────────────┘
```

**依存 DAG の頂点 = #3 (output log-density 可積分性)**。step 1 の `h_int_out` と step 3 の `h_ent_int` の両方を
供給する単一補題で、**唯一の真の Mathlib 不在** (inventory §B: `Integrable (log _) _` / `Integrable (negMulLog _) _`
ともに loogle 0 件)。ただし self-derivable: `rnDeriv_conv` (mixture 密度構造) + Gaussian pdf 上下界 + `q` の二次モーメント
有限 (#2) から組める。その中で **唯一の hard 評価が #3 の下界** `f_q(y) ≥ c·exp(−a·y²)` (Phase 6b、pivot-advisor が唯一
hard 判定) で、これがクリアできれば残り (上界 / 結合 / lift) は機械的。

```
依存 DAG (Phase 番号、矢印 = 依存):

  P1 gaussianPDFReal_le_sup ──┐
                              ├──→ P6a 上界 (log f_q ≤ const)
  P2 output = p∗𝒩 ────────────┤                          │
       │                      └──→ P6b ★mixture 下界 ─────┤
       │                                                  ├──→ P6c |log f_q| ≤ 二次
  P4 Var(Y) ≤ P+N (二次モーメント有限) ─────────────────────┘         │
       │                                                            ├──→ P6d joint lift
  P5 hWx_q (fibre ≪ output) ────────────────────────────────────────┘    │
                                                                          ▼
  P3 log algebra ───────────────────────────────────────────────→ P7 最終結線
                                                                  (chain rule + maxent
                                                                   + Var + 算術 を結ぶ)
```

#3 (Phase 6) が頂点。#1/#5 は Phase 6 の前提素材 (mixture 構造 + fibre≪output)、#2 は二次モーメント有限性の供給、
#1/#6 (easy) は #3 と独立に先行 fill 可能。

### Mathlib-shape-driven 注意 (落とし穴、inventory verbatim)

1. **`differentialEntropy_le_gaussian_of_variance_le` の `m` は真の平均**: `h_var : ∫(x−m)²∂μ ≤ v` は
   `m = ∫y∂q = E[Y]` を取らないと `∫(x−m)²` が分散にならない。**`m := 0` は誤り** (一般 input `p` の `E[X] ≠ 0`)。
   `m := ∫ y, y ∂q` を取り `h_mean : ∫ y, y ∂q = m` を `rfl` で結ぶ。`Var(Y) = ∫(y−E[Y])²∂q ≤ E[Y²] ≤ E[X²]+N`
   (E[Z]=0、Z⟂X) で `v := (P+N).toNNReal`。
2. **chain rule は proxy 形 (教科書 `llr`/`f·log f` 形ではない)**: `mutualInfoOfChannel_toReal_eq_diffEntropy_sub`
   は `g : ℝ×ℝ→ℝ≥0∞` proxy + `h_int_fibre`/`h_int_out` が `Integrable (log (·).toReal) (p⊗ₘW)` 形 (volume 上の
   `f·log f` 形ではない)。AWGN では `g := fun z => gaussianPDF z.1 N z.2` (`measurable_gaussianPDF_uncurry`,
   `ContChannelMIDecomp.lean:370`)。`h_int_fibre` は fibre 側 (`integrable_log_gaussianPDFReal_gaussianReal`,
   `:404`) + `p` 確率測度で free。**`h_int_out` が本壁** (mixture 出力 log-density、Phase 6)。
3. **`gaussianReal x N` (一般 `m≠0` fibre)**: AWGN fibre `W x = gaussianReal x N` (`m=x`)。fibre entropy
   `differentialEntropy_gaussianReal` は分散 `N` のみ依存で `(1/2)log(2πeN)` (mean shift 不変)。`differentialEntropy_dirac = 0`
   等の退化値とは無関係 (N ≠ 0 なので fibre は full-support Gaussian)。

### 規模見積もり (中央予測)

| 自作要素 | inventory # | 難度 | 想定行数 | Phase |
|---|---|---|---|---|
| `gaussianPDFReal_le_sup` (sup 上界 `≤ (√(2πv))⁻¹`) | #5 | easy | ~10-15 | 1 |
| `outputDistribution_awgn_eq_conv` (出力 = `p ∗ 𝒩(0,N)`) | #1 | medium | ~15-25 | 2 |
| log algebra 算術 step | #6 | easy | ~20 | 3 |
| `output_secondMoment_le` + `Var(Y) ≤ P+N` (`h_var`/`h_var_int`) | #2 | medium | ~40-60 | 4 |
| `fibre_absolutelyContinuous_output_general` (`hWx_q`) | #4 | medium | ~20-30 | 5 |
| ★ `outputDistribution_logDensity_integrable` (`h_int_out`/`h_ent_int`) | #3 | **hard** | **~80-150** | 6 |
| 最終結線 `awgn_per_input_mi_le_log` (chain rule + maxent + Var + 算術) | — | medium | ~40-60 | 7 |
| skeleton + imports + docstring + namespace | — | — | ~30-40 | 0 |
| **合計** | | | **~255-400** | |

**中央予測 ~320 行** (inventory §「200-300 行」+ 最終結線 plumbing)。**#3 (Phase 6) が大半**。Phase 6 だけで止まれば
他 6 本は genuine 化済 (壁は #3 1 本に縮約) で type-check done 着地可。

### ファイル構成

```
InformationTheory/Draft/Shannon/
  ContChannelMIDecomp.lean        ← 既存。awgn_capacity_closed_form_of_out (:670) の :692 sorry を
                                     awgn_per_input_mi_le_log 呼出に置換 (Phase 7、本 file 末尾 import 注意)
  AwgnCapacityConverseMaxent.lean ← 新規 (~255-400 行)。#1-#6 + 最終結線
InformationTheory.lean                   ← import InformationTheory.Draft.Shannon.AwgnCapacityConverseMaxent 追記
```

**import 順注意**: `AwgnCapacityConverseMaxent.lean` は `ContChannelMIDecomp.lean` を import する (chain rule
+ proxy 補題を使う)。逆に `ContChannelMIDecomp.lean:692` の結線は **forward reference になるため**、最終結線は
(a) `AwgnCapacityConverseMaxent.lean` 側で `awgn_capacity_closed_form_of_out` を再導出して publish、または
(b) `ContChannelMIDecomp.lean` の当該定理を `AwgnCapacityConverseMaxent.lean` import 後の位置に移設、のいずれか。
**Phase 0 で import 方向を verbatim 確認** (循環回避、CLAUDE.md「依存方向の verbatim 確認」)。中央予測は (a)
(新 file 側に capacity closed-form wrapper を置き、旧 `awgn_capacity_closed_form_of_out` を `@audit:superseded-by`
化 or 旧定理本体を新 file の補題呼出に書換)。

着手 skeleton は inventory §着手 skeleton (L249-300) を base にする (import 9 行 + 4 補題 stub)。

## 撤退ライン

親計画 `awgn-moonshot-plan.md` §撤退ライン **F-3** は既発動済 (n-letter coding converse の per-letter `h_ent_int`
を defer)。本壁は **single-letter capacity converse** (codebook-free `∀ p : Measure ℝ`) で対象が別だが Mathlib gap は同型。
本壁の closure は「F-3 で defer した壁の本体を埋める」前進であり、新規撤退ラインは原則発動しない。ただし #3 (Phase 6)
が書けない場合の段階的縮退を以下に定める。

撤退の段階 (浅い順):

- **[L-CONV-1] #3 (output log-density 可積分性) が当該セッションで書けない** (inventory 提案の正式撤退ライン):
  `outputDistribution_logDensity_integrable` (`h_int_out`/`h_ent_int`) を **shared sorry 補題**として残し、
  `awgn_per_input_mi_le_log` の body は **その補題を `have h_int_out := outputDistribution_logDensity_integrable …`
  で呼び出す形**に書く。chain rule / max-entropy / Var / 算術 (#1/#2/#4/#5/#6) は genuine 化。signature は
  unconditional に保つ。`sorry` は補題側 body に集約 (`@residual(wall:awgn-capacity-converse-maxent)`)。
  **仮説 bundling 禁止** — `h_int_out` を `awgn_per_input_mi_le_log` の hyp 引数に格上げするのは load-bearing
  (証明の核心を仮説に抱えさせる) なので不可 (CLAUDE.md「検証の誠実性」、tier-5 defect)。**regularity 前提
  (`[IsProbabilityMeasure p]` / `hp_2mom`) は補題引数に残す** (落とすと over-general 化で偽、audit-tags.md
  2026-05-28 `contChannelMIDecomp_holds` 教訓)。

- **[L-CONV-2] Phase 6b (mixture 下界 `f_q(y) ≥ c·exp(−a·y²)`) が 2 turn 詰まる**: 下界 sub-lemma を
  `output_logDensity_lower_bound` として shared sorry 補題に切り出し、Phase 6c/6d は上界 + 下界補題の機械的結合で
  genuine 化。**さらに詰まれば L-CONV-1 に縮退** (#3 全体を shared sorry 化)。下界の二次評価は Jensen / Gaussian tail
  経由で `negMulLog` の符号管理 (`f→0` 端と `f` 上界の両側) が煩雑 (inventory §B): 2 turn ループしたら shared sorry に
  逃げる判断点。

- **[L-CONV-3] shared-wall 集約の判断**: 隣接壁 `awgn-per-letter-integrability` (`AwgnWalls.lean:251`) が同型 gap。
  Phase 6 が genuine 着地したら、その本体補題 (Gaussian mixture log-density 可積分性) を **1 本の shared sorry/genuine
  補題に集約**し両壁から参照する (`docs/audit/audit-tags.md`「共有 Mathlib 壁」)。**ただし集約時に regularity 前提
  (二次モーメント有限 / 確率測度 / 絶対連続性) を補題引数から落とさないこと** — `awgn-per-letter-integrability` は
  `converseJointInline` の per-letter pushforward (n-letter joint marginal) で対象 measure が異なるため、両 use-site の
  precondition を引数に残した形で集約する (consumer 側で genuine discharge)。集約が precondition drift を招くなら
  集約せず 2 壁併存のまま (genuine 化を優先)。

**いずれの撤退でも `sorry` は補題 body にのみ残し、`@residual(wall:awgn-capacity-converse-maxent)` を付す**
(L-CONV-3 で集約したら集約後 slug)。signature は unconditional 維持 (load-bearing hyp 禁止)。

## 依存関係

完了済 / 利用可 (inventory API テーブル §A-§D verbatim、`[...]` 前提込み):

- [x] **chain rule (主役)** `InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel_toReal_eq_diffEntropy_sub`
  (`ContChannelMIDecomp.lean:276`, 0 sorry `@audit:ok`)。proxy 形 9 引数。
- [x] **max-entropy (主役)** `differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:520`)。
  `[IsProbabilityMeasure μ]` + `(m:ℝ)` explicit + `h_mean`/`h_var`/`h_var_int`/`h_ent_int`。
- [x] **Gaussian fibre entropy** `differentialEntropy_gaussianReal` (`DifferentialEntropy.lean`, 使用 `:162`)。
- [x] **proxy 可測性** `measurable_gaussianPDF_uncurry` (`ContChannelMIDecomp.lean:370`)。
- [x] **fibre log-pdf 可積分** `integrable_log_gaussianPDFReal_gaussianReal` (`ContChannelMIDecomp.lean:404`)。
- [x] **二次差分 fibre 可積分** `integrable_sq_sub_gaussianReal` (`ContChannelMIDecomp.lean:387`)。
- [x] **bind = conv (任意 SFinite p)** `bind_eq_conv_of_translation_kernel` (`AWGNBindConvBody.lean:78`)。
- [x] **conv 絶対連続** `MeasureTheory.Measure.conv_absolutelyContinuous` (`Convolution.lean:166` 付近, `@[to_additive]`)。
- [x] **conv rnDeriv = lconv** `MeasureTheory.rnDeriv_conv` (`RadonNikodym.lean:653`, `@[to_additive]`、`=ᵐ[μ]`、
  `[SFinite μ] [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] [HaveLebesgueDecomposition]` ×2 + `hν₁`/`hν₂`)。
- [x] **lconv 定義** `MeasureTheory.lconvolution` / `lconvolution_def` (`LConvolution.lean:50`/`:68`)。
- [x] **分散加法** `ProbabilityTheory.IndepFun.variance_add` (`Variance.lean:406`, `MemLp X 2 μ` ×2 + `X ⟂ᵢ Y`)。
- [x] **分散 ≤ 二次モーメント** `ProbabilityTheory.variance_le_expectation_sq` (`Variance.lean:340`, `[IsProbabilityMeasure μ]`)。
- [x] **Gaussian 分散 = v** `ProbabilityTheory.variance_fun_id_gaussianReal` (`Gaussian/Real.lean:518`)。
- [x] **可積分優関数比較** `MeasureTheory.Integrable.mono'` (`L1Space/Integrable.lean`)。
- [x] **snd_compProd / 周辺化** `MeasureTheory.Measure.snd_compProd` (`MeasureComp.lean`)。
- [x] **消費側 sandwich** `awgnCapacity_le_gaussian` (`AWGN.lean:255`)、`awgn_capacity_closed_form_of_out`
  (`ContChannelMIDecomp.lean:670`)。

新規 import (inventory §合計工数感): `Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym` (`rnDeriv_conv`)、
`Mathlib.Analysis.LConvolution` (`lconvolution_def`)、`Mathlib.MeasureTheory.Group.Convolution`
(`conv` / `lintegral_conv` / `conv_absolutelyContinuous`)。Variance / Gaussian 系は既存 import 内。

**Mathlib 不在 (真の壁、`@residual(wall:awgn-capacity-converse-maxent)` 対象、inventory §B/§壁列挙)**:

- `Integrable (fun y => Real.log ((p∗𝒩).rnDeriv vol y).toReal) (p⊗ₘW)` (`h_int_out`) — loogle 0 件、self-derivable (Phase 6)
- `Integrable (fun y => Real.negMulLog ((q.rnDeriv vol y).toReal)) volume` (`h_ent_int`) — 同型、`h_int_out` と本質同一

---

## Phase 0 — signature / 数値 / 在庫差分 verbatim 確認 + skeleton 📋

### スコープ

inventory は十分詳細だが、着手前に 4 点を verbatim verify (CLAUDE.md「具体的数値・型予測の verbatim 確認」
「依存方向の verbatim 確認」):

1. **import 方向 (★最重要、循環回避)**: `ContChannelMIDecomp.lean:692` への結線が forward reference になるため、
   ファイル構成 §の (a)/(b) どちらを取るか確定。`rg "import.*ContChannelMIDecomp\|import.*AwgnCapacity" InformationTheory.lean`
   + 新 file が `ContChannelMIDecomp` を import するときの cycle 有無を `lake env lean` で実機確認。
2. **chain rule の proxy 形 9 引数の正確な型**: `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` (`:276-289`) を Read し、
   `h_int_fibre`/`h_int_out` の被積分関数の正確な形 (`fun z : ℝ × ℝ => Real.log (g z).toReal` /
   `fun z => Real.log ((q.rnDeriv vol z.2).toReal)`) を verbatim 転記。fibre 側 `h_int_fibre` が `p` 確率測度で
   free に出るか (定数 fibre entropy 経由) を確認。
3. **max-entropy の `m` 引数 + 数値**: `differentialEntropy_le_gaussian_of_variance_le` (`:520`) で `m := ∫y∂q` を取った
   とき `h_mean : ∫ y, y ∂q = m` が `rfl` で済むか、`{v : ℝ≥0}` に `(P+N).toNNReal` を入れたとき `hv : v ≠ 0` が
   `P > 0` から出るか。`differentialEntropy_gaussianReal` の結論 `(1/2)log(2πev)` の `v` が分散 (mean 非依存) であることを
   `:162` 使用箇所で確認。
4. **`gaussianPDFReal_le_sup` の sup 値**: inventory 予測 `≤ (Real.sqrt (2 * Real.pi * v))⁻¹` を `gaussianPDFReal` の
   定義 (`Gaussian/Real.lean`) verbatim と照合 (exp 因子 ≤ 1 で `gaussianPDFReal m v y ≤` 正規化定数の形が一致するか)。

### 成果物

- skeleton `InformationTheory/Draft/Shannon/AwgnCapacityConverseMaxent.lean` (inventory §着手 skeleton L249-300 base、
  4 補題 + 最終結線 を `:= by sorry`、全 `sorry` で type-check、各 `sorry` に `@residual(wall:awgn-capacity-converse-maxent)`)
- 本計画書への反映 (import 方向確定 → ファイル構成 §更新、判断ログ #1 候補)

### Done 条件

- skeleton が `lake env lean InformationTheory/Draft/Shannon/AwgnCapacityConverseMaxent.lean` で sorry warning のみ
  (全 補題の statement が型クラス前提込みで通る、import cycle なし)
- 上記 4 点が Read + loogle で裏取り済 (特に import 方向と max-entropy の `m`/`v` 数値)

### 工数感

0.5 セッション。subagent 不要 (inventory 済)、ローカル `Read` / `loogle` のみ。**proof-log**: no (調査 + skeleton のみ)

---

## Phase 1 — `gaussianPDFReal_le_sup` (#5, easy) 📋

### スコープ

`gaussianPDFReal m v y ≤ (Real.sqrt (2 * Real.pi * v))⁻¹`。exp 因子 `exp(−(y−m)²/2v) ≤ 1` (`Real.exp_le_one_iff` /
`Real.exp_nonpos` の負指数) から正規化定数で上から押さえる。Phase 6a (上界 → `log f_q ≤ const`) の素材。

### Done 条件

- `gaussianPDFReal_le_sup (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (y : ℝ) : gaussianPDFReal m v y ≤ (Real.sqrt (2*π*v))⁻¹`
  が 0 sorry (Phase 0 #4 で sup 値が確定した形で)

### 撤退条件

- sup 値が inventory 予測形と違う (`gaussianPDFReal` 定義が正規化定数を別形で持つ) → Phase 0 #4 の verbatim 確認で
  fix 済のはずだが、ズレたら定義 verbatim の形に合わせて statement を修正 (撤退ではなく statement 調整)

**proof-log**: no (easy、~10-15 行)

---

## Phase 2 — `outputDistribution_awgn_eq_conv` (#1, medium) 📋

### スコープ

`outputDistribution p (awgnChannel N h_meas) = p ∗ gaussianReal 0 N` (任意 SFinite `p`)。
`outputDistribution p W = (p⊗ₘW).snd = W ∘ₘ p` (`Measure.snd_compProd`) → `bind_eq_conv_of_translation_kernel`
(in-tree `AWGNBindConvBody.lean:78`、任意 SFinite `p` で genuine) で `= p ∗ 𝒩(0,N)`。Phase 6 で mixture 構造
(`rnDeriv_conv` / `lconvolution`) を使う前提。

### Done 条件

- `outputDistribution_awgn_eq_conv` が 0 sorry (`Measure.snd_compProd` の引数順 + `∘ₘ`/`bind` defeq 処理込み)

### 撤退条件

- `bind_eq_conv_of_translation_kernel` の translation-kernel 形が `awgnChannel` の定義形と直結しない
  (`awgnChannel x = gaussianReal x N` の平行移動構造の同定) → `awgnChannel_apply` (`AWGN.lean:78`) で fibre を展開し、
  translation kernel `κ x = ν.map (· + x)` 形への bridge を 1 補題追加 (~10 行)

**proof-log**: no (medium、in-tree 補題流用、~15-25 行)

---

## Phase 3 — log algebra 算術 step (#6, easy) 📋

### スコープ

`(1/2)*log(2πe(P+N)) − (1/2)*log(2πeN) = (1/2)*log(1+P/N)`。in-tree
`mutualInfoOfChannel_gaussianInput_closed_form` (`AWGN.lean:176-191`) の log 代数を流用
(`Real.log_div` / `Real.log_mul` + `1 + P/N = (P+N)/N`、正値性は `P>0`/`N≠0` から)。

### Done 条件

- 算術補題が 0 sorry (`2πe(P+N)/2πeN = (P+N)/N = 1+P/N` の正値除算 + log_div)

### 撤退条件

- なし (既存パターンのコピー、inventory §自作 #6「落とし穴なし」)

**proof-log**: no (easy、~20 行)

---

## Phase 4 — `output_secondMoment_le` / Var(Y) ≤ P+N (#2, medium) 📋

### スコープ

`h_var : ∫(y−m)²∂q ≤ (P+N)` (`m := ∫y∂q`) + `h_var_int : Integrable (fun y => (y−m)²) q` を供給。
`q = p∗𝒩(0,N)` の `Y = X + Z` (Z⟂X、Z∼𝒩(0,N)、E[Z]=0) 表現で
`Var(Y) = Var(X) + Var(Z) = Var(X) + N ≤ E[X²] + N ≤ P + N`
(`IndepFun.variance_add` + `variance_le_expectation_sq` + `variance_fun_id_gaussianReal`)。`X∼p` の `MemLp 2` は
`∫x²≤P < ∞` から bridge (`memLp_two_iff_integrable_sq` 系)。**`m` は真の平均** (落とし穴、Approach §1)。

### Done 条件

- `h_var`/`h_var_int` を `m := ∫y∂q` 起点で供給する補題群が 0 sorry
- `MemLp X 2 p` を一般 input `p` (二次モーメント有限) から確立する bridge 補題が出ている

### 撤退条件

- `IndepFun.variance_add` を使うための `Y = X+Z` 独立構成 (`q = p∗𝒩` を独立和の law として実現する probability space
  構成) が重い → `Var(Y) ≤ E[Y²]` を `variance_le_expectation_sq` で直に取り、`E[Y²] = E[(X+Z)²] = E[X²]+2E[X]E[Z]+E[Z²]`
  ≤ P + N (E[Z]=0、二次モーメント加法) を畳み込み積分 (`output = p∗𝒩` の二次モーメント = `∫∫(x+z)² d𝒩 dp`) で直接計算する
  経路に切替 (独立空間構成を回避、`lintegral_conv` / `integral_conv` の二次モーメント展開)

**proof-log**: yes (medium、独立空間構成 vs 畳み込み積分直接の判断点、~40-60 行)

---

## Phase 5 — `fibre_absolutelyContinuous_output_general` (#4, medium) 📋

### スコープ

`∀ x, awgnChannel N h_meas x ≪ outputDistribution p (awgnChannel N h_meas)` (一般 `p`)。`hWx_q` を供給。
`q = p∗𝒩(0,N)` は全域正値 (full support) なので `𝒩(x,N) ≪ q`。`q` の full-support を `lconvolution` の正値性
(`q = vol.withDensity f_q`, `f_q > 0` everywhere) から。**in-tree `awgnChannel_apply_absolutelyContinuous_output`
(`ContChannelMIDecomp.lean:353`) は Gaussian 入力専用 (`h_out : IsAwgnOutputGaussian`)、再利用不可** (inventory §主要前提)。

### Done 条件

- `fibre_absolutelyContinuous_output_general` が 0 sorry (`q` full-support → `𝒩(x,N) ≪ q`)
- chain rule の `hWx_q : ∀ x, W x ≪ outputDistribution p W` 引数を埋められる

### 撤退条件

- `q` の everywhere 正値性 (`f_q(y) > 0` ∀y) を `lconvolution_def` の積分正値性から立てるのが重い → Phase 6b で
  どのみち下界 `f_q(y) ≥ c·exp(−a·y²) > 0` を作るので、その下界補題を先行させて `hWx_q` をそこから導く
  (Phase 5 と Phase 6b の順序入替、依存 DAG では 6b → 5 に変わる)

**proof-log**: no (medium、~20-30 行)

---

## Phase 6 — ★ `outputDistribution_logDensity_integrable` (#3, hard, 支配的) 📋

> **本壁の真の核心、唯一の Mathlib 不在 (依存 DAG の頂点)**。inventory §自作 #3「~80-150 行」。
> 4 sub-phase に分割、最難関 6b (mixture 下界) を独立 sub-lemma として隔離。

### Approach (sub-phase 内訳)

mixture 出力密度 `f_q(y) = (p∗𝒩(0,N)).rnDeriv vol y` (Phase 2 + `rnDeriv_conv`、`=ᵐ[vol]`、または直接
`f_q(y) = ∫ gaussianPDFReal x N y ∂p(x)` の `lconvolution`/`lintegral_conv` 形) の `log`/`negMulLog` を、
二次優関数 `c₀ + c₁·y²` で押さえて `q` の二次モーメント有限 (#2) + `Integrable.mono'` で可積分にする。

### 6a — 上界 `log f_q(y) ≤` 定数 📋

`f_q(y) ≤ 1/√(2πN)` (各 component の sup `gaussianPDFReal_le_sup` (#1) を畳み込み積分が継承、`p` 確率測度で
`∫ (√(2πN))⁻¹ ∂p = (√(2πN))⁻¹`) ⟹ `log f_q(y) ≤ −(1/2)log(2πN) < 0`。**上界は定数** (`negMulLog` の `−f log f`
で `f` 上界側の処理)。

- **Done**: `f_q(y) ≤ (√(2πN))⁻¹` everywhere (or ae) + `log f_q ≤ const` が 0 sorry

### 6b — ★ mixture 下界 `f_q(y) ≥ c·exp(−a·y²)` 📋 (唯一の hard、隔離 sub-lemma)

`output_logDensity_lower_bound`: 有限二次モーメント入力 `p` (∫x²≤P) で `f_q(y) ≥ c·exp(−a·y²)` (c>0, a>0)。
pivot-advisor が唯一 hard 判定。`f_q(y) = ∫ gaussianPDFReal x N y ∂p ≥` (Markov/Chebyshev で `p` の質量が
`|x|≤R` に `≥ 1/2` 集中する R を取り、その上で `gaussianPDFReal x N y ≥` Gaussian tail 下界) で
`−log f_q(y) ≤ y²/(2N) + C` の二次オーダー。`p` 二次モーメント有限が R の存在を保証。

- **Done**: `output_logDensity_lower_bound` が 0 sorry (`f_q(y) ≥ c·exp(−a·y²)`、c>0/a>0 明示)
- **撤退 L-CONV-2**: 2 turn 詰まったら本 sub-lemma を shared sorry 補題化 (`@residual(wall:...)`)、6c/6d は機械的結合で genuine 化

### 6c — `|log f_q| ≤ c₀ + c₁·y²` 結合 + `Integrable.mono'` 📋

6a (上界 const) + 6b (下界 → `−log f_q ≤ y²/2N+C`) で `|log f_q(y)| ≤ c₀ + c₁·y²`。`q` の二次モーメント有限
(#2、Phase 4 の `h_var_int` 同型素材) + `Integrable.mono'` で `Integrable (fun y => log f_q(y)) q`。`negMulLog f_q =
−f_q·log f_q` の符号管理 (`f→0` 端 = 6b 下界、`f` 上界 = 6a) はここで集約 (inventory §B「両側評価」)。

- **Done**: `Integrable (fun y => Real.log (f_q y).toReal) q` + `Integrable (fun y => negMulLog (f_q y).toReal) volume` が 0 sorry

### 6d — joint への lift 📋

`h_int_out` (chain rule 形、`p⊗ₘW` 上): `q = (p⊗ₘW).map Prod.snd` 周辺化で `Integrable (log f_q ∘ snd) (p⊗ₘW)`
(`integrable_map_measure` + `measurable_snd`、in-tree `ContChannelMIDecomp.lean:329` 同型)。`h_ent_int`
(max-entropy 形、`volume` 上 `negMulLog`): `q ≪ volume` (`conv_absolutelyContinuous`) で `q`-integrable →
volume-integrable へは `withDensity` 経由 (`q = vol.withDensity f_q`、`negMulLog (f_q) = f_q·(−log f_q)/f_q` の
withDensity 積分変換)。

- **Done**: `outputDistribution_logDensity_integrable` が両形 (`h_int_out` joint / `h_ent_int` volume) で 0 sorry

### Done 条件 (Phase 6 全体)

- `outputDistribution_logDensity_integrable` (`h_int_out`) + max-entropy 用 `h_ent_int` 形が両方 0 sorry
- または L-CONV-1/L-CONV-2 発動で shared sorry 補題に縮約 (`@residual(wall:awgn-capacity-converse-maxent)`)

### 撤退条件

- **6b が 2 turn 詰まる → L-CONV-2** (下界を shared sorry 化、6c/6d は genuine)
- **6 全体が 1 セッション超 → L-CONV-1** (#3 全体を shared sorry 化、他 6 本は genuine 化、signature unconditional 維持)

**proof-log**: yes (`proof-log-awgn-capacity-converse-maxent-phase6.md`。6b mixture 下界の Gaussian tail 評価経路、
`negMulLog` 符号管理、`rnDeriv_conv` ae 基底 vs `lconvolution` 直接形のどちらを取ったか、L-CONV-1/2 発動有無を記録)

---

## Phase 7 — 最終結線 `awgn_per_input_mi_le_log` → `h_max_ent` discharge 📋

### スコープ

Approach §道筋 step 1-5 を結線。chain rule (step 1、proxy 9 引数を Phase 2/5/6 + in-tree fibre 補題で discharge) +
fibre entropy 定数 (step 2) + max-entropy (step 3、Phase 4 + Phase 6 の `h_ent_int`) + Var≤P+N (step 4、Phase 4) +
算術 (step 5、Phase 3) を `linarith`/`calc` で組み、`awgn_per_input_mi_le_log` を publish。
`ContChannelMIDecomp.lean:692` の `sorry` を `exact awgn_per_input_mi_le_log …` に置換 (ファイル構成 § (a)/(b) の
Phase 0 確定形で)。

### Done 条件

- `awgn_per_input_mi_le_log` が 0 sorry (or L-CONV-1 発動なら #3 shared sorry 1 本のみ残、他は genuine)
- `awgn_capacity_closed_form_of_out` (`:670`) の `h_max_ent` が discharge (本壁 closure)
- 旧 `@residual(wall:awgn-capacity-converse-maxent)` が `ContChannelMIDecomp.lean:669` から除去
  (L-CONV-1 なら shared 補題側に移動)

### 撤退条件

- chain rule の `h_int_fibre` (fibre 側) が `p` 確率測度で free に出ない (fibre entropy 定数性の積分化が重い) →
  fibre 側も Phase 6 の二次優関数評価を fibre measure `W x = 𝒩(x,N)` に適用 (`integrable_log_gaussianPDFReal_gaussianReal`
  が直接供給するはずだが、joint `p⊗ₘW` 上の lift で詰まったら `integral_compProd` 経由で fibre 化)

**proof-log**: yes (本壁 closure、判断ログ反映)

---

## Phase V — verify + import + 親 plan F-3 反映 📋

### スコープ

`lake env lean InformationTheory/Draft/Shannon/AwgnCapacityConverseMaxent.lean` clean 確認、
`lake env lean InformationTheory/Draft/Shannon/ContChannelMIDecomp.lean` (結線後 olean refresh 含む) 確認、
`InformationTheory.lean` import 追記、親 plan `awgn-moonshot-plan.md` §撤退ライン F-3 の「single-letter capacity converse
gap を closure した」旨を反映する指示を記録 (実装は lean-implementer、本 plan は反映指示のみ)。L-CONV-3 (隣接壁集約)
判断を記録。

### Done 条件

- 全 Phase の着地状態 (genuine / L-CONV-1/2/3 発動有無) が進捗ブロック + 判断ログに反映
- `@residual(wall:awgn-capacity-converse-maxent)` の最終状態 (0 件 = proof done / 1 件 = shared sorry 集約) を記録
- 独立 honesty audit 起動 (新規 `sorry` + `@residual` 導入 or genuine 着地どちらでも、signature honesty + classification
  検証、CLAUDE.md「Independent honesty audit」)

**proof-log**: no (verify + 反映のみ)

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 着手後に append。想定記録点:
- Phase 0: import 方向 (ファイル構成 (a)/(b)) の確定、max-entropy の m/v 数値 verbatim 確認結果
- Phase 4: Var(Y)≤P+N の独立空間構成 vs 畳み込み積分直接の判断
- Phase 6b: mixture 下界 f_q≥c·exp(−a·y²) の Gaussian tail 評価経路、L-CONV-2 発動有無
- Phase 6: rnDeriv_conv ae 基底 vs lconvolution 直接形の選択、L-CONV-1 発動有無
- Phase 7: chain rule h_int_fibre の free 化可否
- Phase V: L-CONV-3 (隣接壁 awgn-per-letter-integrability 集約) の採否と precondition drift 有無
-->
