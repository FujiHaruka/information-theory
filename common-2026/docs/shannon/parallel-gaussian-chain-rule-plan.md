# Parallel Gaussian L-PG1 genuine discharge ムーンショット計画 🌙 (T2-B payoff)

<!--
雛形メモ (moonshot-plan-template.md より):
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 削除/廃止された Phase は ~~取り消し線~~ で残す（完全削除しない、過去参照のため）
- 判断ログは append-only。Phase 中の方針変更・撤退・当初仮定の修正を記録
- `rg "^- \[ \]"` で残タスク横断 grep、`rg "🔄"` でピボット箇所だけ拾える
-->

> **Parent**: [`parallel-gaussian-moonshot-plan.md`](parallel-gaussian-moonshot-plan.md)
> §撤退ライン **L-PG1** (per-coordinate AWGN F-* hypothesis bundle)。親 plan が
> 「L-PG1 → `parallel-gaussian-chain-rule-plan.md`」と defer 先を明示済 (本ファイル)。
>
> **Bridge 供給元 (今回 payoff の起点)**:
> [`awgn-mi-decomp-plan.md`](awgn-mi-decomp-plan.md) で完成した
> `InformationTheory/Shannon/ContChannelMIDecomp.lean`。段 1 一般 body
> `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` (`:223`, honest 仮定 6 本付き
> 🟢ʰ、**0 sorry genuine**) + linchpin `rnDeriv_compProd_fibre` (`:107`, 🟢
> genuine) を per-coordinate fibre (`gaussianReal xᵢ Nᵢ`) に適用する。
>
> **Status (2026-05-21)**: 着手前。本 plan は **L-PG1
> (`IsParallelGaussianPerCoordReduction`, `ParallelGaussian.lean:235`) を genuine に
> discharge** する。現状の headline `parallel_gaussian_capacity_formula`
> (`ParallelGaussian.lean:277`) は `:= h_per_coord` の完全 pass-through、L-PG1 は
> **結論そのものを Prop 化した OPEN hypothesis** (conclusion-as-hypothesis)。
> water-filling 層 (L-WF1/L-WF2) は別 plan で genuine discharge **済** (下記確認結果)、
> 本 plan は残る情報理論コア L-PG1 のみが対象。

## 着手前 genuine 状態確認 (planner、2026-05-21)

本 plan 着手前に water-filling discharge ファイル群と bridge / max-entropy / chain-rule
の genuine 状態を Read で確認した。結果を本 plan の前提として固定する:

| 資産 | file:line | genuine 状態 | 本 plan での役割 |
|---|---|---|---|
| **段 1 MI 分解 body** `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` | `ContChannelMIDecomp.lean:223` | 🟢ʰ **genuine** (honest 仮定 6 本: `hW_ac`/`hq_ac`/`h_joint_ac`/`h_llr_split`/`h_int_fibre_joint`/`h_int_out_joint`/`h_int_out_marg`) | **per-coord fibre の `I=h(Yᵢ)−h(Zᵢ)`** に直適用 (ステップ2) |
| **linchpin** `rnDeriv_compProd_fibre` | `ContChannelMIDecomp.lean:107` | 🟢 **genuine** | 段 1 body 内部で消費済 (本 plan は段 1 body を呼ぶだけ) |
| **段 2 AWGN instance** `isContChannelMIDecompHyp_awgn` | `ContChannelMIDecomp.lean:357` | 🟢ʰ genuine (residual: `h_meas_fibre` + 3 integrability) | per-coord `gaussianReal` の honest 仮定供給の **手本** |
| **max-entropy** `differentialEntropy_le_gaussian_of_variance_le` | `DifferentialEntropy.lean:510` | 🟢ʰ **genuine** (honest 仮定 `h_mean`/`h_var`/`h_var_int`/`h_ent_int`) | per-coord 上界 `h(Yᵢ)≤(1/2)log(2πe(Varᵢ+Nᵢ))` (ステップ2) |
| **Gaussian entropy 値** `differentialEntropy_gaussianReal` | `DifferentialEntropy.lean:406` | 🟢 genuine | noise 項 `h(Zᵢ)=(1/2)log(2πeNᵢ)` + achiever (ステップ2,3) |
| **MI chain rule (=)** `mutualInfo_pi_eq_sum` | `MIChainRule.lean:341` | 🟢 genuine、ただし **product 入力 i.i.d. factorization 3 本前提で `=` のみ** | **相関入力の優加法性 `≤` は不在** → ステップ1 自作 (最重) |
| **channel↔prod MI** `mutualInfoOfChannel_eq_mutualInfo_prod` | `ChannelCoding.lean:99` | 🟢 genuine (`[IsMarkovKernel W]`) | `mutualInfoOfChannel` ↔ `mutualInfo` 変換 (ステップ1,3) |
| **L-WF1** 存在 `exists_waterFillingKKT_of_pos` | `ParallelGaussianKKT.lean:141` | 🟢 **genuine** (IVT、`Fin (n+1)` nonempty) | sup の電力配分確定 (ステップ4) |
| **L-WF2** 最適性 `waterFillingCertificate_of_lagrange` + `isWFStationarityHyp_of_pos` + `isWFLagrangeBundle_of_KKT` | `WFCertBody.lean:202,261,307` / `WFStationarityBody.lean:104` | 🟢 **genuine** (log-concavity tangent bound + Lagrange) | sup ≤ water-filling sum (ステップ4) |
| **L-PG1** `IsParallelGaussianPerCoordReduction` | `ParallelGaussian.lean:235` | 🔴 **OPEN** (conclusion-as-hypothesis、`:= h_per_coord`) | **本 plan の discharge 対象** |

**重要な前提訂正 (judgement #1 候補)**: 親 plan / `ParallelGaussian.lean:255-262` の
docstring は L-PG1 discharge に「continuous AEP / sphere-shell volume machinery」が必要、
「L-PG1 stays OPEN throughout」と記している。これは**操作的符号化定理** (channel coding
theorem) を念頭にした記述。だが `parallelGaussianCapacity` (`:176`) は実際には
**情報容量** (`sSup { (mutualInfoOfChannel p W).toReal : IsProbabilityMeasure p ∧ ∑ᵢ∫xᵢ²∂p ≤ P }`)
であり、操作的符号化定理ではない。よって L-PG1 の discharge に **continuous AEP は不要**。
max-entropy + MI 優加法性 (上界) + Gaussian achiever (下界) + water-filling (sup 評価) の
4 ステップで genuine に閉じる。本 plan は docstring の「continuous AEP 必要」記述を撤回し、
discharge 完了後に `ParallelGaussian.lean` の docstring 修正を lean-implementer へ指示する
(本 plan は docstring を直接編集しない)。

## 進捗

- [ ] Phase 0 — signature 確認 + MI 優加法性 Mathlib 在庫差分 + skeleton 📋 → [parallel-gaussian-mathlib-inventory.md](parallel-gaussian-mathlib-inventory.md)
- [ ] Phase 1 — **MI 優加法性 (≤、相関入力、最重)** `I(Xⁿ;Yⁿ) ≤ ∑ᵢ I(Xᵢ;Yᵢ)` 📋
- [ ] Phase 2 — per-coord 上界 `I(Xᵢ;Yᵢ) ≤ (1/2)log(1+Varᵢ/Nᵢ)` (bridge + max-entropy) 📋
- [ ] Phase 3 — Gaussian achiever (≥) `parallelGaussianCapacity ≥ ∑ (1/2)log(1+Pᵢ*/Nᵢ)` 📋
- [ ] Phase 4 — water-filling 最適化 (L-WF1/L-WF2 結合) → L-PG1 genuine 📋
- [ ] Phase 5 — headline 再 publish (`parallel_gaussian_capacity_formula` の L-PG1 を discharge 形へ) 📋
- [ ] Phase V — verify + 親 plan / docstring の OPEN 記述更新指示 📋

## ゴール / Approach

### Goal (最終定理 signature)

新規ファイル `InformationTheory/Shannon/ParallelGaussianPerCoord.lean`。L-PG1 を genuine に
証明し、headline の pass-through を discharge 形へ差し替える 2 段:

```lean
namespace InformationTheory.Shannon.ParallelGaussian

open InformationTheory.Shannon.ChannelCoding

/-- ★段 1: L-PG1 genuine discharge。情報容量 `parallelGaussianCapacity` が
per-coord water-filling sum に一致 (honest 解析仮定付き 🟢ʰ)。

honest 仮定は per-coord Gaussian fibre の MI 分解 bridge + max-entropy が要求する
正則性 (measurability + integrability)、AWGN(#5) と共有 (下記 §honest 仮定表)。 -/
theorem isParallelGaussianPerCoordReduction_discharged {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin (n + 1) → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (ν : ℝ) (h_kkt : IsWaterFillingKKT P N ν)
    -- honest 解析仮定 (per-coord Gaussian regularity、AWGN と共有、🟢ʰ)
    (h_reg : IsParallelGaussianPerCoordRegularity P N h_meas h_parallel_meas) :
    IsParallelGaussianPerCoordReduction P N h_meas h_parallel_meas ν

/-- ★段 2: headline の L-PG1 引数を段 1 で discharge した再 publish。 -/
theorem parallel_gaussian_capacity_formula_discharged {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin (n + 1) → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (h_reg : IsParallelGaussianPerCoordRegularity P N h_meas h_parallel_meas) :
    parallelGaussianCapacity P N h_meas h_parallel_meas
      = ∑ i : Fin (n + 1), (1/2) *
          Real.log (1 + waterFillingPower (Classical.choose
            (exists_waterFillingKKT_of_pos P hP N)) N i / (N i : ℝ))

end InformationTheory.Shannon.ParallelGaussian
```

> **signature 落とし穴 (judgement #2 候補)**: L-WF1 存在補題
> `exists_waterFillingKKT_of_pos` (`KKT.lean:141`) は **`Fin (n+1)`** (nonempty 必須、
> IVT の端点構成に nonempty 利用) で立っている。本 plan の段 1/段 2 も `Fin (n+1)` に
> 揃える。`n=0` (空チャネル) は sup={0}、別 corollary か `Fin n` 一般版は Phase 0 で
> nonempty 不要経路を検討 (`n=0` は容量 0 = water-filling sum 0 で trivial)。

### Approach (overall strategy / shape of solution)

**戦略の shape**: L-PG1 = `parallelGaussianCapacity = ∑ᵢ (1/2)log(1+waterFillingPower/Nᵢ)`
は **情報容量 (sSup) の評価**。sup の **上界 (≤)** と **下界 (≥)** を別々に押さえ、
antisymmetry で `=` にする。上界は「任意の入力 law での MI を per-coord に分解して
max-entropy で押さえる」、下界は「独立 Gaussian 入力という具体的 achiever を構成」。
最後に water-filling 最適化 (genuine 既存) で配分を `waterFillingPower ν` に確定する。

continuous AEP は **不要**: 操作的符号化定理ではなく情報容量公式なので、符号化器の
存在ではなく「MI の sup = closed form」だけ示せばよい。これが本 payoff が成立する核心。

```
┌──────────────────────────────────────────────────────────────────────────────┐
│ ステップ1 [Phase 1] ★最重  MI 優加法性 (≤、相関入力)                          │
│   任意 prob 入力 p on (Fin (n+1) → ℝ) と memoryless parallel channel に対し    │
│     I(Xⁿ;Yⁿ) ≤ ∑ᵢ I(Xᵢ;Yᵢ)                                                  │
│   出力が条件付き独立 (`parallelGaussianChannel` = `Measure.pi` fibre) ⇒        │
│   出力エントロピー subadditivity + 条件付き等号 で組む。                        │
│   `mutualInfo_pi_eq_sum` (MIChainRule:341) は product 入力で `=` のみ ⇒        │
│   相関入力の `≤` は別途 (出力独立性 + conditioning reduces entropy)。          │
├──────────────────────────────────────────────────────────────────────────────┤
│ ステップ2 [Phase 2]  per-coord 上界                                          │
│   各 I(Xᵢ;Yᵢ) ≤ (1/2)log(1+Varᵢ/Nᵢ):                                         │
│     ─ 段 1 bridge `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` で          │
│         I(Xᵢ;Yᵢ) = h(Yᵢ) − h(Zᵢ)  (Zᵢ = noise = gaussianReal 0 Nᵢ fibre)     │
│     ─ max-entropy `differentialEntropy_le_gaussian_of_variance_le` で         │
│         h(Yᵢ) ≤ (1/2)log(2πe(Varᵢ+Nᵢ))                                       │
│     ─ `differentialEntropy_gaussianReal` で h(Zᵢ)=(1/2)log(2πeNᵢ)            │
│     ─ 引き算で (1/2)log((Varᵢ+Nᵢ)/Nᵢ) = (1/2)log(1+Varᵢ/Nᵢ)                  │
├──────────────────────────────────────────────────────────────────────────────┤
│ ステップ3 [Phase 3]  Gaussian achiever (≥)                                   │
│   独立 Gaussian 入力 p* := Measure.pi (i ↦ gaussianReal 0 Pᵢ*) で            │
│     各 I(Xᵢ;Yᵢ) = (1/2)log(1+Pᵢ*/Nᵢ)  (等号、bridge + Gaussian entropy 値)   │
│   ⇒ p* は制約集合の要素 (∑∫xᵢ²∂p* = ∑Pᵢ* ≤ P) ⇒                            │
│     parallelGaussianCapacity ≥ ∑ I(Xᵢ;Yᵢ) = ∑ (1/2)log(1+Pᵢ*/Nᵢ)            │
│   (sSup の `le_csSup` + image membership)                                     │
├──────────────────────────────────────────────────────────────────────────────┤
│ ステップ4 [Phase 4]  water-filling 最適化 + antisymmetry                     │
│   L-WF1 `exists_waterFillingKKT_of_pos` で ∑ waterFillingPower ν = P を満たす  │
│     ν を取る。Pᵢ* := waterFillingPower ν N i で achiever 下界を確定。         │
│   上界 (ステップ1+2 の任意入力評価) を L-WF2 `IsWaterFillingOptimal` で       │
│     ∑ (任意配分の log) ≤ ∑ (water-filling の log) に押さえ、                  │
│     csSup ≤ ∑ (water-filling の log) を `csSup_le` で。                       │
│   下界 (ステップ3) = 上界 ⇒ antisymmetry で L-PG1 `=`。                       │
└──────────────────────────────────────────────────────────────────────────────┘
```

**核心 1 (sup の上下界分離)**: L-PG1 は `sSup … = closed form`。
`Real.le_antisymm` で 2 方向に割る:
- `≤`: `Real.csSup_le` (image nonempty + 上界) ← ステップ1 (任意入力 MI 優加法性) +
  ステップ2 (per-coord 上界) + ステップ4 上界部 (L-WF2)。
- `≥`: `Real.le_csSup` (bddAbove + member) ← ステップ3 (Gaussian achiever) +
  ステップ4 下界部 (L-WF1 で配分 = water-filling)。
`bddAbove` (csSup 動作に必須) は上界 `∑ (1/2)log(1+Varᵢ/Nᵢ)` を介して別補題で確保
(ステップ2 上界が `Var` で押さえられない場合は制約 `∑∫xᵢ²≤P` から `Varᵢ ≤ P` で bound)。

**核心 2 (bridge を per-coord fibre に乗せる、Mathlib-shape-driven)**: 段 1 bridge
`mutualInfoOfChannel_toReal_eq_diffEntropy_sub` は **任意の Markov channel `W : Channel ℝ ℝ`**
の density-level 恒等式。per-coord では `W := awgnChannel Nᵢ` (= `gaussianReal · Nᵢ` fibre)
に適用 ⇒ honest 仮定 6 本は `gaussianReal` の事実で充足 (`isContChannelMIDecompHyp_awgn`
`ContChannelMIDecomp.lean:357` が AWGN で全 discharge 済の手本)。**per-coord は AWGN(#5)
の 1 次元 case そのもの** ⇒ bridge + AWGN discharge をそのまま再利用、新規の解析は最小。

**核心 3 (最重 = ステップ1 の MI 優加法性)**: `mutualInfo_pi_eq_sum` (MIChainRule:341)
は **product 入力** (joint/X/Y の 3 つの i.i.d. factorization 仮定) で `=` のみ。相関入力
での `≤` (優加法性) は Mathlib にも InformationTheory にも不在。これを自作する。経路:

```
I(Xⁿ;Yⁿ) = h(Yⁿ) − h(Yⁿ|Xⁿ)
  h(Yⁿ|Xⁿ) = ∑ᵢ h(Yᵢ|Xᵢ)   ← channel memoryless: 出力 fibre 独立 (Measure.pi)、
                                条件付きエントロピー加法 (条件付き独立 ⇒ =)
  h(Yⁿ) ≤ ∑ᵢ h(Yᵢ)          ← 出力エントロピー subadditivity (差分エントロピー版)
⇒ I(Xⁿ;Yⁿ) = h(Yⁿ) − ∑ᵢ h(Yᵢ|Xᵢ) ≤ ∑ᵢ h(Yᵢ) − ∑ᵢ h(Yᵢ|Xᵢ) = ∑ᵢ I(Xᵢ;Yᵢ)
```

差分エントロピー subadditivity (`h(Yⁿ) ≤ ∑ h(Yᵢ)`) が Mathlib に無ければ、これが
本 plan の最大の自作。**推定 ~150-250 行**、rabbit hole 化のリスク最大 (Phase 0 で
Mathlib 在庫を確定、無ければ撤退ラインへ)。

### honest 仮定 (per-coord Gaussian regularity、🟢ʰ)

段 1 bridge + max-entropy が要求する正則性を 1 つの predicate
`IsParallelGaussianPerCoordRegularity` にまとめ、honest 仮定として段 1/段 2 に渡す。
AWGN(#5) の `isContChannelMIDecompHyp_awgn` (`ContChannelMIDecomp.lean:357`) と
`differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:510`) の
residual と **完全に共有** (新規の honest 仮定は増やさない):

| honest 仮定 | 供給元 | 共有先 |
|---|---|---|
| per-coord fibre density measurability `h_meas_fibre` | `isContChannelMIDecompHyp_awgn` residual | AWGN #5 |
| per-coord 3 integrability (fibre/out joint + out marg) | 同上 | AWGN #5 |
| max-entropy `h_var_int` / `h_ent_int` | `differentialEntropy_le_gaussian_of_variance_le` honest | maxent |
| input 2 次モーメント `∫xᵢ²∂p` の存在 (制約 well-defined) | 制約集合定義 | — |

AWGN 側で residual を unconditional に潰せた範囲 (Gaussian moment bound) は per-coord でも
同じ Gaussian 事実で潰せるので、最終的に段 1 の honest 仮定は **measurability 1 本 +
integrability 数本** に縮む見込み (🟢ʰ)。**sorry は厳禁** (CLAUDE.md 撤退ライン規約)。

### 段階的着地見込み

| | 着地見込み | 主リスク |
|---|---|---|
| **ステップ1 (MI 優加法性 ≤)** | 中。差分エントロピー subadditivity が Mathlib にあれば 🟢、無ければ自作 ~150-250 行 | **唯一の山場**。>250 行化したら段階着地 (下記撤退ライン D-1) |
| **ステップ2 (per-coord 上界)** | 🟢ʰ genuine 見込み。bridge + max-entropy の直結 (per-coord = AWGN 1 次元 case) | bridge の honest 仮定 plumbing (Gaussian で充足) |
| **ステップ3 (achiever ≥)** | 🟢ʰ genuine 見込み。独立 Gaussian の MI = bridge + Gaussian entropy 値で等号 | `Measure.pi` 入力での `∑∫xᵢ²` 計算、image membership |
| **ステップ4 (water-filling)** | 🟢 genuine。L-WF1/L-WF2 既存 discharge を結合するだけ | csSup/csInf の bddAbove 整合 |

### 規模見積もり (中央予測)

| 自作要素 | 想定行数 | Phase |
|---|---|---|
| skeleton + imports + docstring + namespace | ~40-60 | 0 |
| **ステップ1 MI 優加法性 (≤、相関入力)** | **~150-250** | 1 |
| ステップ2 per-coord 上界 (bridge + maxent 接続、per-coord = AWGN case) | ~80-130 | 2 |
| ステップ3 Gaussian achiever (≥、image membership + Gaussian MI 等号) | ~70-120 | 3 |
| ステップ4 water-filling 結合 + antisymmetry + bddAbove | ~60-100 | 4 |
| `IsParallelGaussianPerCoordRegularity` predicate + honest 仮定 bundle | ~30-50 | 1-2 |
| 段 2 headline 再 publish (`parallel_gaussian_capacity_formula_discharged`) | ~20-40 | 5 |
| **合計** | **~450-750** | |

**中央予測 ~580 行** (ステップ1 が支配項)。**段階着地** (ステップ1 を honest 仮定化
した D-1) なら ~330 行で per-coord 上界 + achiever + water-filling の genuine 部分を publish。

### ファイル構成

新規 `InformationTheory/Shannon/ParallelGaussianPerCoord.lean`:

```
InformationTheory/Shannon/
  ContChannelMIDecomp.lean     ← 既存。段 1 body (:223) / linchpin (:107) / AWGN instance (:357) を再利用 (変更なし)
  DifferentialEntropy.lean     ← 既存。max-entropy (:510) / Gaussian entropy (:406) を再利用 (変更なし)
  MIChainRule.lean             ← 既存。mutualInfo_pi_eq_sum (:341) を product achiever で再利用 (変更なし)
  ChannelCoding.lean           ← 既存。mutualInfoOfChannel_eq_mutualInfo_prod (:99) (変更なし)
  ParallelGaussian.lean        ← 既存。L-PG1 def (:235) / capacity (:176) / 主定理 (:277) を import (変更なし、docstring 修正は Phase V 指示のみ)
  ParallelGaussianKKT.lean     ← 既存。L-WF1 (:141) / L-WF2 reduction (:235) を再利用 (変更なし)
  ParallelGaussianWFCertBody.lean ← 既存。L-WF2 lagrange (:202) を再利用 (変更なし)
  ParallelGaussianPerCoord.lean ← 新規 (~450-750 行)。L-PG1 genuine discharge + headline 再 publish
InformationTheory.lean                ← import InformationTheory.Shannon.ParallelGaussianPerCoord 追記 (Phase V、オーケストレータ)
```

**新規 import (`ParallelGaussianPerCoord.lean`、CLAUDE.md `Import Policy` 厳守、pinpoint)**:

```lean
import InformationTheory.Shannon.ParallelGaussian
import InformationTheory.Shannon.ParallelGaussianKKT
import InformationTheory.Shannon.ContChannelMIDecomp
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.ChannelCoding
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
```

## 依存関係

完了済 / 利用可 (着手前確認結果、§着手前 genuine 状態確認 参照):

- [x] **`ContChannelMIDecomp.lean`**: `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` (`:223`, 段 1 body 🟢ʰ), `rnDeriv_compProd_fibre` (`:107`, linchpin 🟢), `isContChannelMIDecompHyp_awgn` (`:357`, AWGN discharge 手本)
- [x] **`DifferentialEntropy.lean`**: `differentialEntropy_le_gaussian_of_variance_le` (`:510`, max-entropy 🟢ʰ), `differentialEntropy_gaussianReal` (`:406`, Gaussian entropy 値 🟢), `differentialEntropy_eq_integral_density` (`:60`)
- [x] **`MIChainRule.lean`**: `mutualInfo_pi_eq_sum` (`:341`, product 入力 `=` 🟢、achiever で利用)
- [x] **`ChannelCoding.lean`**: `mutualInfoOfChannel_eq_mutualInfo_prod` (`:99`), `mutualInfoOfChannel` (`:84`), `outputDistribution` (`:71`), `jointDistribution` (`:54`)
- [x] **`ParallelGaussian.lean`**: `parallelGaussianCapacity` (`:176`), `parallelGaussianChannel` (`:94`), `IsParallelGaussianPerCoordReduction` (`:235`, L-PG1 def), `waterFillingPower` (`:129`), 主定理 (`:277`)
- [x] **`ParallelGaussianKKT.lean`**: `exists_waterFillingKKT_of_pos` (`:141`, L-WF1 🟢), `isWaterFillingOptimal_of_certificate` (`:235`, L-WF2 reduction), `IsWaterFillingKKT`/`IsWaterFillingOptimal` 利用
- [x] **`ParallelGaussianWFCertBody.lean`** / **`WFStationarityBody.lean`**: L-WF2 genuine cert (`:202`/`:104`)
- [x] **Mathlib `MeasureTheory.Constructions.Pi`**: `Measure.pi`, `Measure.pi_pi`, `Measure.integral_pi` (achiever の `∫xᵢ²` 計算)
- [x] **Mathlib `Probability.Distributions.Gaussian.Real`**: `gaussianReal`, `variance_id_gaussianReal`, `gaussianReal_absolutelyContinuous`

**要 Phase 0 確認 (在庫差分)**:

- 差分エントロピー **subadditivity** `h(Yⁿ) ≤ ∑ h(Yᵢ)` の Mathlib 有無 (ステップ1 の核、loogle で確定、無ければ自作)
- **条件付き差分エントロピー** `h(Yⁿ|Xⁿ) = ∑ h(Yᵢ|Xᵢ)` (memoryless ⇒ fibre 独立) の表現手段 (bridge の `∫ h(W x) dp` 形で代替可能か)
- `Real.csSup_le` / `Real.le_csSup` / `csSup` の `bddAbove`・`Set.Nonempty` 前提と `parallelGaussianCapacity` の image の整合

---

## Phase 0 — signature 確認 + MI 優加法性 Mathlib 在庫差分 + skeleton 📋

### スコープ

着手前に 3 点を loogle + Read で verify:

1. **差分エントロピー subadditivity の在庫** (ステップ1 撤退判断の前提): `h(X,Y) ≤ h(X)+h(Y)`
   の連続版が Mathlib にあるか (`differentialEntropy` ベース or `MeasureTheory` の entropy)。
   無ければ KL ≥ 0 (joint vs product) 経由で自作する経路を skeleton に確保。**ここが Phase 1 の規模を決める**。
2. **per-coord = AWGN 1 次元 case の同一視**: `parallelGaussianChannel N` の fibre
   `i ↦ gaussianReal (x i) (N i)` が `awgnChannel (N i)` の出力 law と一致する射影
   (`Measure.pi` の i 成分 marginal = `gaussianReal (x i) (N i)`) を `Measure.map_pi_apply`
   系で取れるか確認 (ステップ2/3 で bridge を per-coord に乗せる接続点)。
3. **sup の上下界 API**: `Real.csSup_le` (image nonempty 前提) / `Real.le_csSup` (bddAbove 前提)
   の正確な前提と、`parallelGaussianCapacity` の image (`{ p | … }`) が nonempty
   (iid Gaussian が制約集合に入る) + bddAbove (上界 = per-coord 上界の和) であることの確認。

### 成果物

- skeleton `InformationTheory/Shannon/ParallelGaussianPerCoord.lean` (段 1 / 段 2 + 補助補題を
  `:= by sorry`、`IsParallelGaussianPerCoordRegularity` predicate 含む、全 `sorry` で type-check)
- 本計画書への反映 (差分エントロピー subadditivity の在庫有無 → Approach 核心 3 / 撤退ライン D-1 の更新)

### Done 条件

- skeleton が `lake env lean` で sorry warning のみ (`Fin (n+1)` の型クラス前提込みで statement 全通過)
- 差分エントロピー subadditivity の在庫有無が確定、Phase 1 の経路 (Mathlib 直 / 自作) が判断ログに記録

### 工数感

0.5 セッション。subagent 不要 (inventory 済 + 本 plan の着手前確認済)、ローカル `loogle` / `Read`。**proof-log**: no (調査 + skeleton)

---

## Phase 1 — MI 優加法性 (≤、相関入力) ★最重 📋

### スコープ

ステップ1。任意 prob 入力 `p : Measure (Fin (n+1) → ℝ)` と `parallelGaussianChannel N`
に対し `(mutualInfoOfChannel p (parallelGaussianChannel N …)).toReal ≤ ∑ᵢ I(Xᵢ;Yᵢ)`。
出力 fibre 独立 (`Measure.pi`) を使って `I = h(Yⁿ) − h(Yⁿ|Xⁿ)` を per-coord に分解:
`h(Yⁿ|Xⁿ) = ∑ h(Yᵢ|Xᵢ)` (memoryless 等号) + `h(Yⁿ) ≤ ∑ h(Yᵢ)` (subadditivity)。

### Done 条件

- 補題 `mutualInfoOfChannel_le_sum_perCoord` (相関入力 `≤`) が genuine (honest 仮定付き 🟢ʰ)
- 差分エントロピー subadditivity が Mathlib 直 or 自作で確立 (KL ≥ 0 経路含む)

### 撤退条件 (= 本 plan の主撤退判断点)

- 差分エントロピー subadditivity の自作が **>250 行 rabbit hole** 化 → **撤退ライン D-1 発動**:
  ステップ1 (MI 優加法性) を honest 仮定 `IsParallelGaussianMISuperadditive` として段 1 に残し、
  ステップ2-4 (per-coord 上界 + achiever + water-filling) は genuine に閉じる段階着地。
  product 入力での `=` (`mutualInfo_pi_eq_sum` 既存) で sup の **達成側 (≥)** は genuine、
  上界 (≤) のみ honest 仮定。それでも 🟢ʰ で現状 (`:= h_per_coord` 完全 pass-through) より前進。

**proof-log**: yes (Phase 1 完了 or D-1 撤退のどちらでも append、判断ログ #3 候補)

---

## Phase 2 — per-coord 上界 (bridge + max-entropy) 📋

### スコープ

ステップ2。各 `I(Xᵢ;Yᵢ) ≤ (1/2)log(1+Varᵢ/Nᵢ)`。per-coord fibre = AWGN 1 次元 case:
- 段 1 bridge `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` で `I(Xᵢ;Yᵢ) = h(Yᵢ) − h(Zᵢ)`
- max-entropy `differentialEntropy_le_gaussian_of_variance_le` で `h(Yᵢ) ≤ (1/2)log(2πe(Varᵢ+Nᵢ))`
- `differentialEntropy_gaussianReal` で `h(Zᵢ) = (1/2)log(2πeNᵢ)`
- 引き算 + `Real.log_div` で `(1/2)log(1+Varᵢ/Nᵢ)`

### Done 条件

- 補題 `mutualInfoOfChannel_perCoord_le_log` (per-coord 上界) が genuine 🟢ʰ
- honest 仮定が `IsParallelGaussianPerCoordRegularity` に集約 (AWGN #5 / maxent と共有)

### 撤退条件

- per-coord bridge の honest 仮定 (Gaussian fibre measurability + integrability) の Gaussian
  discharge が重い → AWGN side (`isContChannelMIDecompHyp_awgn`) の residual をそのまま
  honest 仮定として持ち上げ (新規仮定は増やさない、🟢ʰ)

**proof-log**: yes

---

## Phase 3 — Gaussian achiever (≥) 📋

### スコープ

ステップ3。独立 Gaussian 入力 `p* := Measure.pi (i ↦ gaussianReal 0 (waterFillingPower ν N i).toNNReal)`
で各 `I(Xᵢ;Yᵢ) = (1/2)log(1+Pᵢ*/Nᵢ)` (等号、bridge + Gaussian entropy 値)。`p*` が制約集合の
要素 (`∑∫xᵢ²∂p* = ∑Pᵢ* ≤ P`、`variance_id_gaussianReal` + `Measure.integral_pi`) ⇒
`mutualInfo_pi_eq_sum` (product 入力 `=`) で全 MI = `∑ (1/2)log(1+Pᵢ*/Nᵢ)` ⇒
`Real.le_csSup` で `parallelGaussianCapacity ≥ ∑`。

### Done 条件

- 補題 `parallelGaussianCapacity_ge_sum_perCoord` (achiever 下界) が genuine 🟢ʰ
- `p*` の image membership (制約 `∑∫xᵢ²≤P` 充足) + `bddAbove` (csSup well-defined) が確立

### 撤退条件

- `Measure.pi` 入力での `∫ xᵢ² ∂p*` の per-coord marginal 計算 (`Measure.integral_pi` /
  `variance_id_gaussianReal`) の plumbing が重い → 制約を `∑ Var ≤ P` の honest 仮定形に縮退
  (achiever 構成自体は維持、moment 計算のみ仮定化)

**proof-log**: yes

---

## Phase 4 — water-filling 最適化 + antisymmetry → L-PG1 genuine 📋

### スコープ

ステップ4。L-WF1 `exists_waterFillingKKT_of_pos` で `∑ waterFillingPower ν = P` を満たす `ν`
を取り `Pᵢ* := waterFillingPower ν N i`。上界 (Phase 1+2 の任意入力評価) を L-WF2
`IsWaterFillingOptimal` で `∑ (任意配分 log) ≤ ∑ (water-filling log)` に押さえ `csSup_le` で
上界、Phase 3 achiever で下界、`Real.le_antisymm` で L-PG1 `=`。

### Done 条件

- `isParallelGaussianPerCoordReduction_discharged` (段 1) が genuine 🟢ʰ (`Fin (n+1)`)
- 上界 (csSup_le) + 下界 (le_csSup) + antisymmetry が完結、`IsParallelGaussianPerCoordReduction` を返す

### 撤退条件

- 上界部で「任意入力の per-coord 上界の和」を L-WF2 の `IsWaterFillingOptimal` 形に流し込む際、
  `Varᵢ` (任意入力の per-coord 分散) を `Pᵢ'` (L-WF2 の自由配分) に同定する整合が詰まる →
  per-coord 分散配分の存在を honest 仮定 (`∃ P', ∀i Varᵢ ≤ P'ᵢ ∧ ∑P'ᵢ ≤ P`) に縮退

**proof-log**: yes (L-PG1 着地、判断ログ反映)

---

## Phase 5 — headline 再 publish 📋

### スコープ

段 2。`parallel_gaussian_capacity_formula_discharged`: 段 1 で L-PG1 を discharge し、
headline `parallel_gaussian_capacity_formula` (`ParallelGaussian.lean:277`) の `h_per_coord`
引数を `isParallelGaussianPerCoordReduction_discharged` で埋めた再 publish を `Fin (n+1)` で publish。
L-WF1/L-WF2 も既存 discharge で埋め、honest 仮定は `IsParallelGaussianPerCoordRegularity` のみ。

### Done 条件

- `parallel_gaussian_capacity_formula_discharged` が genuine 🟢ʰ (honest 仮定 = per-coord regularity のみ)
- 0 sorry / 0 warning

**proof-log**: yes (headline discharge 着地)

---

## Phase V — verify + 親 plan / docstring の OPEN 記述更新指示 📋

### スコープ

- `lake env lean InformationTheory/Shannon/ParallelGaussianPerCoord.lean` clean (0 errors / 0 sorry / 警告最小)
- `InformationTheory.lean` への import 追記は **オーケストレータ側** (本 plan はルートを触らない)
- **lean-implementer への指示**: `ParallelGaussian.lean:255-262` 主定理 docstring の
  「L-PG1 stays OPEN throughout」「continuous AEP / sphere-shell volume machinery absent」を
  discharge 状態に更新 (情報容量公式は continuous AEP 不要、本 plan で genuine discharge 済)。
  親 plan `parallel-gaussian-moonshot-plan.md` 冒頭の実態整合ブロックも同様に更新指示。
  **本 plan は他ファイルの docstring / 親 plan 本文を直接編集しない** (反映は実装者と親 planner)。

### Done 条件

- 全 Phase の着地状態 (段 1 / 段 2 / 撤退発動有無) が進捗ブロック + 判断ログに反映
- 親 plan L-PG1 への discharge リンクが本 plan から張られている

**proof-log**: no (verify + 反映指示のみ)

---

## 撤退ライン

親計画 `parallel-gaussian-moonshot-plan.md` §撤退ライン **L-PG1**:
`IsParallelGaussianPerCoordReduction` を hypothesis pass-through。現状 headline は
`:= h_per_coord` の完全 pass-through (conclusion-as-hypothesis OPEN)。本 plan はこれを
genuine 化する。撤退の段階 (浅い順):

- **[D-1] ステップ1 (MI 優加法性 ≤) が rabbit hole (>250 行)**: ステップ1 を honest 仮定
  `IsParallelGaussianMISuperadditive`(任意入力で `I(Xⁿ;Yⁿ) ≤ ∑I(Xᵢ;Yᵢ)`) として段 1 に残し、
  ステップ2-4 を genuine に閉じる。**上界 (≤) のみ仮定化、下界 (≥) は achiever で genuine**。
  product 入力での MI = ∑ (`mutualInfo_pi_eq_sum` 既存) で達成側は genuine ⇒ L-PG1 の
  `≥` 方向は無条件、`≤` 方向のみ MI 優加法性 honest 仮定経由。**現状の完全 conclusion-as-hypothesis
  より明確に前進** (sup の半分 + per-coord 上界 + water-filling が genuine、残り 1 仮定)。
- **[D-2] per-coord bridge / max-entropy の honest 仮定が Gaussian で潰せない**: per-coord
  regularity (`h_meas_fibre` + integrability) を named honest 仮定として段 1 に残す (🟢ʰ)。
  AWGN(#5) と共有なので本 plan 独自の仮定は増えない。**ステップ 1-4 の骨格 (sup 評価構造) は genuine**。
- **[D-3] sup の上下界 API (csSup_le / le_csSup) の bddAbove / nonempty が型壁**: L-PG1 を
  hypothesis pass-through のまま温存 (`ParallelGaussian.lean:235` 据え置き)。本 plan は
  inventory + skeleton + 型壁の正確な記録のみ publish。

**いずれの撤退でも `sorry` は残さない** (honest pass-through / 明示 hypothesis signature で
抜ける。CLAUDE.md 撤退ライン規約)。

## Risk Table

| # | リスク | 確率 | 影響 | 緩和策 |
|---|---|---|---|---|
| 1 | 差分エントロピー subadditivity `h(Yⁿ)≤∑h(Yᵢ)` が Mathlib にない | 高 | Phase 1 +150-250 行 | KL≥0 (joint vs product) 経路で自作 / D-1 撤退 (MI 優加法性 honest 仮定化) |
| 2 | per-coord fibre = `awgnChannel (N i)` の同一視 (`Measure.pi` i-marginal) が `Measure.map_pi` で取れない | 中 | ステップ2/3 接続 +50 行 | Phase 0 で marginal lemma 確定、無ければ手動 push-forward |
| 3 | `Real.csSup_le` / `le_csSup` の bddAbove / nonempty 前提が image で示せない | 中 | ステップ4 +40 行 | bddAbove = per-coord 上界の和、nonempty = iid Gaussian member (Phase 0 確認) |
| 4 | bridge の honest 仮定 (per-coord Gaussian integrability) の plumbing が AWGN side で未 discharge の residual に依存 | 中 | 🟢ʰ honest 仮定 +数本 | AWGN(#5) と共有、新規仮定を増やさず `IsParallelGaussianPerCoordRegularity` に集約 |
| 5 | achiever `Measure.pi (gaussianReal 0 Pᵢ*)` の `∑∫xᵢ²` 計算 (`variance_id_gaussianReal` + `integral_pi`) plumbing | 中 | ステップ3 +40 行 | moment 計算を honest 仮定形に縮退 (achiever 構成は維持) |
| 6 | `Fin (n+1)` 縛り (L-WF1 nonempty) で `n=0` / 一般 `Fin n` が別扱い | 低 | corollary +20 行 | `n=0` は容量 0 = sum 0 で trivial、`Fin (n+1)` を主形に |
| 7 | L-WF2 `IsWaterFillingOptimal` の自由配分 `P'ᵢ` に任意入力の per-coord 分散 `Varᵢ` を同定する整合 | 中 | ステップ4 +50 行 | per-coord 分散配分の存在を honest 仮定に縮退 (Phase 4 撤退条件) |

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **判断 #1 (planner、着手前)**: `ParallelGaussian.lean:255-262` docstring の「L-PG1 discharge
   に continuous AEP / sphere-shell volume が必要、stays OPEN throughout」記述を撤回。
   `parallelGaussianCapacity` (`:176`) は情報容量 (`sSup` of MI) であり操作的符号化定理ではない
   ⇒ continuous AEP 不要、max-entropy + MI 優加法性 + Gaussian achiever + water-filling で genuine
   に閉じる。docstring 修正は Phase V で lean-implementer / 親 planner へ指示 (本 plan は直接編集せず)。
2. **判断 #2 (planner、着手前)**: 段 1/段 2 を **`Fin (n+1)`** で立てる。L-WF1 存在補題
   `exists_waterFillingKKT_of_pos` (`KKT.lean:141`) が IVT 端点構成に nonempty を要求するため。
   `n=0` (空チャネル) は容量 0 = water-filling sum 0 で trivial、必要なら別 corollary。
3. **判断 #3 (着手前確認、water-filling 層 genuine 確定)**: L-WF1 (`exists_waterFillingKKT_of_pos`,
   IVT) / L-WF2 (`waterFillingCertificate_of_lagrange` + `isWFStationarityHyp_of_pos` log-concavity
   tangent + `isWFLagrangeBundle_of_KKT`) は **既に genuine discharge 済** (`KKT.lean` / `WFCertBody.lean`
   / `WFStationarityBody.lean`、0 sorry)。本 plan はステップ4 でこれらを結合するのみ、water-filling
   最適化の新規証明は不要。残る OPEN は情報理論コア L-PG1 のみ。

<!-- Phase 着手後に append: 差分エントロピー subadditivity の Mathlib 在庫有無 (Phase 0)、
D-1 (MI 優加法性 honest 仮定化) 発動有無 (Phase 1)、honest 仮定の最終本数、per-coord = AWGN
case 同一視の成否 (Phase 2)、achiever moment 計算の成否 (Phase 3) がここに記録される見込み。 -->
