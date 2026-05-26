# AWGN Converse aux — F-3 analytic discharge ムーンショット計画 🌙 (T2-A Tier-3 follow-up)

<!--
雛形メモ (moonshot-plan-template.md / subplan-template.md):
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)`
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更
- 取り消し / 廃止 Phase は ~~取り消し線~~ で残す
- 判断ログは append-only
-->

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) §「撤退ライン F-3」
> (per-letter integrability + chain rule + per-letter Gaussian max-entropy bundle)
> + 判断ログ 確定済 #1 (4 撤退ライン全採用 publish)。
>
> **Sibling plans (scope 直交)**:
> [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md) — F-1 (achievability core、580 行 genuine assembly + 3 bundled staged hyps、完走)。
> [`awgn-mi-bridge-plan.md`](awgn-mi-bridge-plan.md) — F-2 (channel MI ↔ `h(Y) − h(Y|X)` 形 bridge、stub)。
> [`awgn-mi-decomp-plan.md`](awgn-mi-decomp-plan.md) — F-2 deeper layer (continuous channel MI chain rule の genuine discharge、AWGN-agnostic body 補題)。
> [`awgn-f1-f3-peer-simultaneous-migration-plan.md`](awgn-f1-f3-peer-simultaneous-migration-plan.md) — Round 4 escalate #1 で F-1/F-3 を peer 同時に第一選択 migration、当該 sweep の出口に本 plan が位置する (本 plan は signature 改変後の analytic body 完成 = `awgn_converse` body の `sorry` を埋める作業)。
> [`awgn-f1-discharge-moonshot-plan.md`](awgn-f1-discharge-moonshot-plan.md) — F-4 (kernel measurability、完了 148 行)。
>
> **Status (2026-05-27)**: 起草中 (本 plan は Lean code を書かず Phase 構造のみを定義)。
> 起草前の起点は `awgn-converse-aux-plan.md` の Tier 3 stub (2.7 KB、`docs/shannon/awgn-converse-aux-plan.md` の 2026-05-24 版)。
> F-1/F-3 peer 同時第一選択 migration (2026-05-27 commit) により
> `IsAwgnConverseHypothesis` predicate は **削除済**、
> `Common2026/Shannon/AWGNConverse.lean:59-70` の `awgn_converse` body は
> `sorry` + `@residual(plan:awgn-converse-aux-plan)` + `@audit:closed-by-successor(awgn-converse-aux-plan)`
> の Tier 2 状態。本 plan の責務はその `sorry` を **analytic body** で genuine
> discharge することに完全に絞られる (signature 改変は完了済)。
>
> **Goal**: `Common2026/Shannon/AWGNConverseDischarge.lean` 新規 publish (姉妹
> `AWGNAchievabilityDischarge.lean` と対称命名)。最終 signature は:
>
> ```lean
> namespace InformationTheory.Shannon.AWGN
>
> /-- F-3 撤退ラインの本物 discharge (Cover-Thomas 9.1.2 の Lean 化)。 -/
> theorem isAwgnConverseFeasible_discharger
>     (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
>     (h_meas : IsAwgnChannelMeasurable N)
>     (h_feasible : IsAwgnConverseFeasible P N h_meas)   -- bundle of analytic primitives (T-FFC-2 staged hyp、姉妹と対称)
>     {M n : ℕ} (hM : 2 ≤ M) (c : AwgnCode M n P)
>     (Pe : ℝ)
>     (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
>         (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
>     Real.log M
>       ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
>         + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := …
>
> /-- `awgn_converse` の `sorry` を埋める薄い wrapper。 -/
> theorem awgn_converse_F3_discharged
>     (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
>     (h_meas : IsAwgnChannelMeasurable N)
>     (h_feasible : IsAwgnConverseFeasible P N h_meas)
>     {M n : ℕ} (hM : 2 ≤ M) (c : AwgnCode M n P) (Pe : ℝ) (hPe : …) :
>     … := isAwgnConverseFeasible_discharger P hP N hN h_meas h_feasible hM c Pe hPe
>
> end InformationTheory.Shannon.AWGN
> ```
>
> 最終的に `Common2026/Shannon/AWGNConverse.lean:70` の `sorry` は
> `isAwgnConverseFeasible_discharger` への呼出に置換され、`@residual(plan:awgn-converse-aux-plan)`
> は `@audit:staged(awgn-converse-feasible)` 等に降格 (staged hyp 1 本 = bundle predicate
> の Mathlib 壁残置)。Tier 2 sorry が消えるが、staged hyp の closure はさらに後続 plan
> (`awgn-converse-feasible-discharge-plan.md` — まだ未起草) に委ねる **2 段構成**。
>
> **撤退ライン (本 plan 内)**: [T-FFC-1] Fano `fano_inequality_measure_theoretic` の
> `[StandardBorelSpace (Fin n → ℝ)]` 型クラス自動推論失敗 → local instance 提供で吸収 /
> [T-FFC-2] per-letter integrability `h_ent_int` の Mathlib 壁 → bundle predicate
> `IsAwgnConverseFeasible` の staged hyp として packing (姉妹 `IsAwgnRandomCodingFeasible`
> と同型 pattern) / [T-FFC-3] continuous MI chain rule
> `I(X^n; Y^n) ≤ ∑ I(X_i; Y_i)` の Mathlib 壁 (memoryless channel reuse) → 同 bundle へ
> 集約 / [T-FFC-4] 規模超過 (~500 行超) → 2 file 分割 (Fano + DPI を `…Fano.lean`、
> chain + per-letter を `…Perletter.lean`)。詳細 §撤退ライン。
>
> **honesty 規律**: 本 plan の目的は `awgn_converse` body sorry を **analytic body** で
> 埋めること。`IsAwgnConverseFeasible` bundle は姉妹 `IsAwgnRandomCodingFeasible` と同
> 型の **regularity / Mathlib-wall packaging** であって load-bearing claim ではない。
> 4 条件 (CLAUDE.md「検証の誠実性」/ audit-tags.md「Mathlib 壁 4 分類」): (a) bundle の
> 結論型 ≠ `awgn_converse` の結論 `log M ≤ n·C + binEntropy(Pe) + …` / (b) Mathlib 壁
> 明示 (per-letter `h_ent_int` Integrable / continuous MI chain rule の memoryless 化 /
> DPI for continuous Y) / (c) 本 file Phase B が bundle を destructure し Fano + chain
> + per-letter bound で genuine assembly / (d) `@audit:staged(awgn-converse-feasible)`
> タグ付与。

## 進捗

- [ ] Phase 0 — Mathlib + Common2026 在庫 (Fano measure form / DPI continuous / continuous MI chain rule / Gaussian Y max-entropy / per-letter integrability) 📋 → [`awgn-converse-aux-mathlib-inventory.md`](awgn-converse-aux-mathlib-inventory.md) (本 plan で同時起草、subagent 依頼)
- [ ] Phase A — bundle predicate `IsAwgnConverseFeasible` 設計 + skeleton 📋
- [ ] Phase B-Fano — Fano application via `fano_inequality_measure_theoretic` (`X := Fin M`, `Y := Fin n → ℝ`) 📋
- [ ] Phase B-DPI/chain — DPI `I(W;Ŵ) ≤ I(X^n;Y^n)` + memoryless chain `I(X^n;Y^n) ≤ ∑ I(X_i;Y_i)` 📋
- [ ] Phase B-Gaussian — per-letter `I(X_i;Y_i) ≤ (1/2) log(1+P/N)` (Gaussian Y_i max-entropy) 📋
- [ ] Phase C — `isAwgnConverseFeasible_discharger` 統合 + `awgn_converse_F3_discharged` wrapper 📋
- [ ] Phase V — verify (lake env lean silent / 0 sorry / 1 staged bundle / `AWGNConverse.lean` の `sorry` を呼出に置換 / `Common2026.lean` 編入) 📋

## ゴール / Approach

### Goal (最終定理 signature、再掲)

現状 (peer 同時 migration 後 = 起点):

```lean
-- Common2026/Shannon/AWGNConverse.lean:59-70 (2026-05-27 commit)
theorem awgn_converse
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (hM : 2 ≤ M) (c : AwgnCode M n P) (Pe : ℝ)
    (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  sorry  -- @residual(plan:awgn-converse-aux-plan), @audit:closed-by-successor
```

本 plan の最終形:

```lean
namespace InformationTheory.Shannon.AWGN

/-- **AWGN converse feasibility bundle** (Cover-Thomas 9.1.2 schema、姉妹
`IsAwgnRandomCodingFeasible` の converse 対応版)。Fano + DPI + memoryless chain
rule + per-letter Gaussian max-entropy を 1 bundle に packing し、Mathlib 壁
(per-letter integrability + continuous MI chain rule) を staged hyp として外出
し。 -/
def IsAwgnConverseFeasible (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ {M n : ℕ} (_hM : 2 ≤ M) (c : AwgnCode M n P),
    -- "core analytic primitives" のみ要求、結論型は出さない:
    -- ① per-letter input law marginal の Gaussian dominance
    -- ② per-letter `Y_i` の `Integrable (negMulLog (rnDeriv ...))` (Mathlib 壁)
    -- ③ continuous-MI chain rule reuse (memoryless channel 形)
    -- ④ DPI for `W → X^n → Y^n → Ŵ` (continuous Y_n、Fano 入力 `X := Fin M`)
    PerLetterIntegrabilityForConverse P N h_meas c ∧
    ContinuousMIChainRuleForConverse P N h_meas c ∧
    DPIForConverse P N h_meas c

/-- F-3 撤退ラインの本物 discharge (Cover-Thomas 9.1.2 の Lean 化)。 -/
theorem isAwgnConverseFeasible_discharger
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_feasible : IsAwgnConverseFeasible P N h_meas)
    {M n : ℕ} (hM : 2 ≤ M) (c : AwgnCode M n P) (Pe : ℝ)
    (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  -- destructure bundle、Fano + DPI + chain + per-letter で組み立て
  …

/-- `awgn_converse` の `sorry` を埋める薄い wrapper。 -/
theorem awgn_converse_F3_discharged …
end InformationTheory.Shannon.AWGN
```

`IsAwgnConverseFeasible` の **structure / field 構成は Phase 0 inventory + Phase A
着手時の判断 #1 で確定**。上記は schema として 3 sub-bound 形を示すが、姉妹
`IsAwgnRandomCodingFeasible` のように `∃` で `P'` 等の witness を共有させる必要性が
あるかは Phase 0 で再評価する (converse 側は input law がコードブック非依存なので
witness 不要、3 sub-bound の単純連言で済む見込み)。

### Approach (overall strategy / shape of solution)

**戦略**: Cover-Thomas 9.1.2 (Theorem 9.1.2 converse) の標準 4 段 (Fano → DPI →
memoryless chain rule → per-letter Gaussian max-entropy) をそのまま Lean に転写。
各段を独立 Phase に割り当て、Phase 間の界面型は Phase 0 inventory で先に確定する
(skeleton-driven, CLAUDE.md)。姉妹 achievability discharge と同型の
**bundle-predicate packing** で Mathlib 壁を 1 staged hyp に集約 (姉妹は
`IsAwgnRandomCodingFeasible` 3 sub-bound 形)。

```
(a) Fano's inequality (measure-theoretic form)         [Phase B-Fano]
    H(W | Ŵ) ≤ H(Pe) + Pe · log(|X| − 1)
    where X = Fin M, Y = Fin n → ℝ, decoder : Y → X
    → fano_inequality_measure_theoretic (Common2026/Fano/Measure.lean:226) 直接呼出

(b) Data processing inequality                          [Phase B-DPI]
    I(W; Ŵ) ≤ I(X^n; Y^n)
    (W → X^n encoder deterministic、Y^n → Ŵ decoder measurable、Markov chain)
    → 既存 Common2026 DPI? 在庫確認 (Phase 0)、不在なら bundle 内 staged hyp に格納

(c) Memoryless channel chain rule                       [Phase B-chain]
    I(X^n; Y^n) ≤ ∑ᵢ I(Xᵢ; Yᵢ)
    (AWGN channel is memoryless: Y^n = X^n + Z^n、Z_i iid)
    → Common2026/Shannon/ChannelCodingConverseMemorylessPure.lean を schema 参考
       (`Fintype α` 壁あり、AWGN α := ℝ は直接 reuse 不可)
    → bundle 内 staged hyp に格納 (continuous channel chain rule の Mathlib 壁)

(d) Per-letter Gaussian max-entropy bound               [Phase B-Gaussian]
    I(Xᵢ; Yᵢ) = h(Yᵢ) − h(Yᵢ | Xᵢ) = h(Yᵢ) − h(N)
              ≤ (1/2) log(2πe(P + N)) − (1/2) log(2πeN)
              = (1/2) log(1 + P/N)
    → differentialEntropy_le_gaussian_of_variance_le (4-hypothesis 形) +
       differentialEntropy_gaussianReal +
       per-letter integrability h_ent_int (bundle 内 staged hyp)
    → I = h(Y) − h(Y|X) bridge は F-2 (awgn-mi-bridge / awgn-mi-decomp) と共有

(e) 合成 + 算術                                         [Phase C]
    log M = H(W) (W uniform on Fin M)
          = H(W | Ŵ) + I(W; Ŵ)                  (entropy chain rule)
          ≤ H(Pe) + Pe · log(M-1) + I(X^n; Y^n)  (Fano + DPI)
          ≤ H(Pe) + Pe · log(M-1) + ∑ I(Xᵢ; Yᵢ)  (chain rule)
          ≤ H(Pe) + Pe · log(M-1) + n · (1/2) log(1+P/N)  (per-letter)
```

**Mathlib-shape-driven definitions** (CLAUDE.md、本 plan 起草前に verbatim 確認済):

- **Fano** — `fano_inequality_measure_theoretic` (`Common2026/Fano/Measure.lean:226`)
  は **`condEntropy μ Xs Yo ≤ binEntropy Pe + Pe · log(card X − 1)`** を返す。
  本 plan の `awgn_converse` 結論 `log M ≤ n·C + binEntropy Pe + Pe · log(M − 1)`
  に直結する形 ⇒ そのまま使える (X := Fin M `Fintype` finite、Y := Fin n → ℝ
  continuous、Fano の Y 側に制約なし)。verbatim 確認: `fano_inequality_measure_theoretic`
  signature 引数 `(μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Ω → X) (Yo : Ω → Y)
  (decoder : Y → X) (hXs hYo hdec) (hcard : 2 ≤ Fintype.card X)`、結論
  `condEntropy μ Xs Yo ≤ binEntropy (errorProb μ Xs Yo decoder) + errorProb … · log (card X − 1)`。
  注意: AWGN converse は **average error** `Pe = (1/M) ∑ errorProbAt m` を入れた `log M`
  bound、Fano は `errorProb` 直接 (= `μ.map (X, Yo, decoder) ≠ 0` 確率)。両者の同値性
  bridge は標準 (uniform W + measurable encoder/decoder)、Phase B-Fano 内で 20-40 行。

- **per-letter Gaussian max-entropy** — `differentialEntropy_le_gaussian_of_variance_le`
  (`Common2026/Shannon/DifferentialEntropy.lean:518`、4-hypothesis 形) で
  `Y_i ∼ μ_{Y_i}` `[IsProbabilityMeasure μ_{Y_i}]` `(hμ : μ_{Y_i} ≪ volume) (h_mean h_var
  h_var_int h_ent_int)` から `differentialEntropy μ_{Y_i} ≤ (1/2) log(2πe(P+N))` を取る。
  **`h_ent_int : Integrable (negMulLog (rnDeriv μ_{Y_i} volume)) volume`** が per-letter
  で discharge 不能 (input law μ_i に依存) ⇒ bundle 内 staged hyp に格納 (T-FFC-2)。
  Y_i marginal が AWGN なので `Y_i = X_i + Z_i ∼ X_i ∗ N(0,N)` で convolution、`hμ ≪ volume`
  は Gaussian noise convolve から自動 (`gaussianReal_absolutelyContinuous` + Phase A
  既存)。`h_mean h_var h_var_int` は input power constraint `∑ (X_i)² ≤ nP` から
  per-letter `E[X_i²] ≤ P` で導出可 (Cauchy-Schwarz、~20 行)。

- **continuous MI chain rule** — Common2026 既存
  `condMutualInfo_chain_rule_X_2var`、`channel_coding_converse_general_memoryless_strong`
  (`Common2026/Shannon/ChannelCodingConverseGeneralStrong.lean:276`、`Fintype α`) は
  `α := ℝ` で直接 reuse 不可。AWGN-agnostic continuous chain rule は **Mathlib 壁** ⇒
  bundle 内 staged hyp `ContinuousMIChainRuleForConverse` に格納 (T-FFC-3)。これは
  姉妹 `awgn-mi-decomp-plan.md` の Phase 6 一般 body 補題と相補関係 — 同 plan が
  closure すれば本 staged hyp も自動 discharge 候補。

- **DPI for continuous Y** — `fano_inequality_measure_theoretic` から
  `condEntropy μ W Ŵ ≤ …` を経由した後、`H(W) ≤ H(W | Ŵ) + I(W; Ŵ)` の `I(W; Ŵ)`
  を `I(X^n; Y^n)` で上から押さえる DPI が必要。Common2026 在庫は Phase 0 で要 verbatim
  確認 (`MutualInfo.lean` / `CondMutualInfo.lean` / `MIChainRule.lean` 周辺、loogle
  `mutualInfo_le_mutualInfo_of_measurable` 等)。不在なら bundle 内 staged hyp
  `DPIForConverse` に格納。**注意**: encoder `W → X^n` は deterministic
  (`c.encoder : Fin M → Fin n → ℝ`)、decoder `Y^n → Ŵ` は measurable
  (`c.decoder_meas`)、両者で `Y^n` が `(W, Ŵ)` の中間 → DPI は標準的に強い形で出る
  はず、Mathlib 壁ではない可能性。

### 規模見積もり

| Phase | 内容 | 楽観 | 中央 | 悲観 (壁発動) |
|---|---|---:|---:|---:|
| Phase 0 | inventory (別 file) | 0 (Lean) | 0 | 0 |
| Phase A | skeleton + bundle predicate | 80 | 120 | 180 |
| Phase B-Fano | Fano application + errorProb bridge | 60 | 100 | 150 |
| Phase B-DPI/chain | DPI + memoryless chain | 80 | 150 | 250 |
| Phase B-Gaussian | per-letter Gaussian bound + arith | 120 | 180 | 250 |
| Phase C | 統合 + wrapper | 30 | 50 | 80 |
| skeleton + plumbing | (各 Phase の skeleton 部分) | 30 | 50 | 80 |
| **合計** | | **~400** | **~650** | **~990** |

中央予測 **~650 行**。姉妹 achievability discharge (1641 行、3 staged hyp bundle +
580 行 E-1 body) より小さい — converse は Fano + chain rule + per-letter という
標準形で、achievability の sphere packing + codebook average + expurgation のような
randomization 工程が無いため。判断 #1 でこの規模感を再確認する。

T-FFC-4 発動条件: 1000 行超過 → 2 file 分割
(`AWGNConverseDischargeFano.lean` ~250 + `AWGNConverseDischargePerletter.lean` ~400)。

### ファイル構成

```
Common2026/Shannon/
  AWGNConverseDischarge.lean   ← 新規 (本 plan 出力、~650 行)
                                  Phase A-C を 1 file 集約
  AWGNConverse.lean (既存)      ← 本 plan の sorry 置換対象 (line 70)
  AWGN.lean (既存)              ← awgnChannel / AwgnCode / IsAwgnChannelMeasurable
  AWGNMain.lean (既存)          ← 主定理 wrapper (本 plan 完了後 import 経路追加)
  AWGNF1Discharge.lean (既存)   ← F-4 (kernel measurability)、独立完了
  DifferentialEntropy.lean (既存) ← Phase B-Gaussian で利用
  ChannelCoding.lean (既存)     ← Channel / Code / mutualInfoOfChannel
  MutualInfo.lean (既存)        ← typed RV 形 MI
  CondMutualInfo.lean (既存)    ← cond MI + chain rule
  MIChainRule.lean (既存)       ← per-letter chain rule schema (Fintype α 壁あり)
Common2026/Fano/
  Measure.lean (既存)           ← fano_inequality_measure_theoretic
Common2026.lean                 ← 1 行 import 追加 (Phase V、オーケストレータ実施)
docs/shannon/
  awgn-converse-aux-mathlib-inventory.md  ← Phase 0 出力 (本 plan で起草指示、subagent)
  awgn-converse-aux-plan.md               ← 本 plan
  proof-log-awgn-converse-aux-phase[A-C].md  ← Phase 単位 (yes 指定 Phase のみ)
```

**imports** (CLAUDE.md `Import Policy` 厳守、`import Mathlib` 禁止):

```lean
import Common2026.Meta.EntryPoint
import Common2026.Shannon.AWGN
import Common2026.Shannon.AWGNConverse           -- sorry 置換のため必須
import Common2026.Shannon.AWGNF1Discharge        -- (optional) isAwgnChannelMeasurable で wrapper 統合する場合のみ
import Common2026.Shannon.DifferentialEntropy    -- differentialEntropy_le_gaussian_of_variance_le
import Common2026.Shannon.ChannelCoding          -- Channel / Code / mutualInfoOfChannel / errorProbAt
import Common2026.Shannon.MutualInfo             -- mutualInfo typed RV form
import Common2026.Shannon.CondMutualInfo         -- condEntropy / condMutualInfo
import Common2026.Shannon.MIChainRule            -- per-letter chain rule schema
import Common2026.Fano.Measure                   -- fano_inequality_measure_theoretic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LpSpace.Basic
-- 追加 import は Phase 0 inventory + Phase 着手時 loogle で確定
```

## 依存関係 (Mathlib + Common2026 既存)

完了済 / 利用可:

- **Fano** — `Common2026/Fano/Measure.lean:226`
  `fano_inequality_measure_theoretic` (verbatim 確認済、§Approach 参照)。
  4 引数 (Xs, Yo, decoder + measurability triple) + 1 hcard、結論 `condEntropy ≤
  binEntropy + Pe · log(card-1)` の形。
- **per-letter Gaussian max-entropy** — `Common2026/Shannon/DifferentialEntropy.lean:518`
  `differentialEntropy_le_gaussian_of_variance_le` (verbatim 確認済、4-hypothesis 形、
  `h_ent_int` のみ staged 対象)。
- **Gaussian entropy closed form** — `Common2026/Shannon/DifferentialEntropy.lean:412`
  `differentialEntropy_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    differentialEntropy (gaussianReal m v) = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)`
  (verbatim 確認済)。
- **channel MI** — `Common2026/Shannon/ChannelCoding.lean:85`
  `mutualInfoOfChannel p W := klDiv (jointDistribution p W) (p.prod (outputDistribution p W))`
  (verbatim 確認済)。`mutualInfoOfChannel_eq_mutualInfo_prod` (line 96) で typed
  RV 形 MI と等価変換可。
- **AWGN definitions** — `Common2026/Shannon/AWGN.lean:64-100` `IsAwgnChannelMeasurable`
  `awgnChannel` `AwgnCode` (encoder, decoder, decoder_meas, power_constraint)。
- **achievability discharge** — `Common2026/Shannon/AWGNAchievabilityDischarge.lean`
  (1641 行、姉妹) — `IsAwgnRandomCodingFeasible` bundle pattern を本 plan の
  `IsAwgnConverseFeasible` 設計時に参考。

**Phase 0 で裏取り必要** (Mathlib + Common2026 在庫、subagent inventory 必須):

- DPI for continuous Y — `mutualInfo_le_of_measurable_*`、`condMutualInfo` 経由の
  Markov chain DPI、`klDiv` 上の DPI (`klDiv_le_of_kernel_apply` 等)。AWGN-agnostic
  形式が現存するか / 不在なら bundle 内 staged hyp に格納するか確定。
- continuous MI chain rule for memoryless channel —
  `Common2026/Shannon/ChannelCodingConverseGeneralStrong.lean:276`
  `channel_coding_converse_general_memoryless_strong` の `Fintype α` 壁を
  どう剥がすか確認 (T-FFC-3 staged or T-FFC-3 incremental discharge)。
- per-letter input law marginal の Gaussian dominance — power constraint
  `∑ (X_i)² ≤ nP` ⇒ per-letter `E[X_i²] ≤ P` の Cauchy-Schwarz 経由 bridge。
- per-letter integrability `h_ent_int` の Mathlib 壁判定 — `Integrable
  (negMulLog (rnDeriv μ_{Y_i} volume)) volume` の Mathlib 一般定理在庫
  (Gaussian-mixture density の有界 + 急減衰、`differentialEntropy_le_gaussian_*` の
  通常 hypothesis 形がそのまま staged の母体)。
- entropy chain rule `H(W) = H(W | Ŵ) + I(W; Ŵ)` — `Common2026/Shannon/MutualInfo.lean`
  / `CondMutualInfo.lean` / `Entropy.lean` 周辺。`mutualInfo_eq_entropy_sub_condEntropy`
  形が在庫にあるか。
- `H(W) = log M` for uniform W on `Fin M` — `Common2026/Shannon/Entropy.lean`
  `entropy_uniform` 系の在庫確認。

**参考 (import しない / schema のみ)**:

- `Common2026/Shannon/ChannelCodingConverseGeneralComplete.lean` (`Fintype α` 想定、
  AWGN α := ℝ で直接 reuse 不可、schema 参考のみ)。
- `Common2026/Shannon/ChannelCodingConverseGeneralStrong.lean` (同上)。
- `Common2026/Shannon/ChannelCodingConverseMemorylessPure.lean` (同上)。
- `Common2026/Shannon/AWGNAchievabilityDischarge.lean` (姉妹 achievability、本 file
  の bundle pattern 設計時の構造参考)。

---

## Phase 0 — Mathlib + Common2026 API 在庫 📋

### スコープ

`docs/shannon/awgn-converse-aux-mathlib-inventory.md` 新規 (~300-500 行 MD)。
本 plan 固有の 5 軸 (Fano 適用 / DPI continuous / continuous MI chain rule /
per-letter Gaussian max-entropy / per-letter integrability) について Mathlib +
Common2026 在庫を **per-lemma 構造化形式** で裏取り (CLAUDE.md「Subagent Inventory
of Mathlib Lemmas」: `file:line` + 完全 signature + `[...]` type-class verbatim +
結論形 verbatim 厳守)。subagent 起動時は **`mathlib-inventory` agent** を使う。

### Done 条件

- [ ] inventory file 新規作成 (`awgn-converse-aux-mathlib-inventory.md`)
- [ ] 5 軸ごとに「既存 / 部分既存 / 不在」を判定
- [ ] **判断 #1 (bundle predicate `IsAwgnConverseFeasible` の structure)** —
      Mathlib + Common2026 在庫を見て、bundle 内 staged sub-bound 数 (2 〜 4)、
      witness の必要性 (姉妹 achievability bundle は `∃ P'` witness を持つが、
      converse は input law がコードブック非依存なので不要見込み)、各 sub-bound
      の field 型を確定。
- [ ] **判断 #2 (entropy chain rule + uniform W bridge の在庫)** —
      `H(W) = log M` (W uniform on `Fin M`) + `H(W) = H(W | Ŵ) + I(W; Ŵ)`
      (entropy chain rule) が Common2026 既存ならそのまま使う、不在なら
      Phase B-Fano 内で局所構築。
- [ ] **判断 #3 (DPI continuous の壁判定)** —
      `I(W; Ŵ) ≤ I(X^n; Y^n)` で `Y^n : Fin n → ℝ` continuous を扱う DPI 補題
      の存在判定。在庫があれば genuine discharge、不在なら bundle 内 staged hyp。
- [ ] **判断 #4 (continuous MI chain rule の壁判定)** —
      `I(X^n; Y^n) ≤ ∑ I(X_i; Y_i)` for memoryless AWGN channel。
      `awgn-mi-decomp-plan.md` Phase 6 一般 body 補題と相補。在庫 / 部分在庫 /
      不在を確定。
- [ ] **判断 #5 (per-letter integrability `h_ent_int` の壁形式)** —
      `Integrable (negMulLog (rnDeriv μ_{Y_i} volume)) volume` を per-letter で
      要求するか、bundle 内 1 件で「全 `i : Fin n` について」forall に packing
      するか。後者なら姉妹 `IsAwgnPowerConstraintHonest` と同型の packing pattern。

### proof-log

no (inventory MD のみ)。

### 工数感

0.5-1 session。失敗時 fallback: inventory を 5 軸別 file に分割 (姉妹 plan は 5
file 分割した: `axis1` / `axis2` / `axis3` / `axis4` / `axis5`)。

### 失敗時 fallback

- 5 軸全て Mathlib 壁判定 → bundle 内 staged hyp が 4 件以上に膨張 → 判断 #1 で
  bundle pivot (姉妹 `IsAwgnRandomCodingFeasible` のように 1 bundle に 4 sub-bound
  を集約、honesty 4 条件は維持)。
- inventory 起草中に Common2026 既存補題に load-bearing hyp / circular def を発見 →
  CLAUDE.md「検証の誠実性」に従い即フラグ + 本 plan の依存対象から外す。

---

## Phase A — bundle predicate `IsAwgnConverseFeasible` 設計 + skeleton 📋

### スコープ

`Common2026/Shannon/AWGNConverseDischarge.lean` 新規作成 (skeleton + Phase A 本体)。

- A-0 skeleton write (Phase A-C 全主定理を `:= by sorry` で並べる)
- A-1 sub-bound predicate 群定義 (3-4 件、判断 #1 確定後)
- A-2 `IsAwgnConverseFeasible P N h_meas` bundle 定義 (3-4 sub-bound の連言)
- A-3 honesty 4 条件 docstring (姉妹 `IsAwgnRandomCodingFeasible` と同型 4 条件)
- A-4 `@audit:staged(awgn-converse-feasible)` タグ付与

### 入出力型 (key、判断 #1 で確定後 update 予定)

```lean
/-- per-letter Y_i (= X_i + Z_i) の Gaussian max-entropy integrability + density
事項を per-letter で要求する bundle field (Mathlib 壁 T-FFC-2)。 -/
def PerLetterIntegrabilityForConverse (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) {M n : ℕ} (c : AwgnCode M n P) : Prop :=
  ∀ i : Fin n,
    -- per-letter input law (W uniform → encoder marginal)
    let μ_Xi : Measure ℝ := … (uniform W 上の encoder marginal)
    let μ_Yi : Measure ℝ := μ_Xi.bind (fun x => awgnChannel N h_meas x)
    -- power constraint per-letter (Cauchy-Schwarz)
    (∫ x, x^2 ∂μ_Xi ≤ P) ∧
    -- Gaussian max-entropy 4 hypotheses (3 of 4、`h_ent_int` のみ wall)
    (μ_Yi ≪ volume) ∧
    (Integrable (fun y => y^2) μ_Yi) ∧
    -- ★ Mathlib 壁: integrability of -p log p for Y_i density
    Integrable (fun y => Real.negMulLog ((μ_Yi.rnDeriv volume y).toReal)) volume

/-- DPI: `I(W; Ŵ) ≤ I(X^n; Y^n)` for continuous Y^n (W uniform on Fin M、
encoder deterministic、decoder measurable)。Mathlib 壁判定は Phase 0 判断 #3。 -/
def DPIForConverse (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) {M n : ℕ} (c : AwgnCode M n P) : Prop :=
  ∀ (uniformW : Measure (Fin M)) [_h_unif : IsProbabilityMeasure uniformW],
    (∀ w : Fin M, uniformW {w} = (1 / M : ℝ≥0∞)) →   -- W uniform
    -- I(W; Ŵ) ≤ I(X^n; Y^n) 形 (具体形は Phase 0 で確定)
    sorry

/-- continuous MI chain rule for memoryless AWGN: `I(X^n; Y^n) ≤ ∑ I(X_i; Y_i)`。
Mathlib 壁 (`awgn-mi-decomp-plan.md` と相補)。 -/
def ContinuousMIChainRuleForConverse (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) {M n : ℕ} (c : AwgnCode M n P) : Prop :=
  ∀ (uniformW : Measure (Fin M)) [IsProbabilityMeasure uniformW],
    -- I(X^n; Y^n) ≤ ∑ I(X_i; Y_i) 形 (具体形は Phase 0 で確定)
    sorry

/-- **AWGN converse feasibility bundle** (姉妹 `IsAwgnRandomCodingFeasible` と
対称、Mathlib 壁の analytic primitives 集約)。3 sub-bound の連言。 -/
def IsAwgnConverseFeasible (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ {M n : ℕ} (_hM : 2 ≤ M) (c : AwgnCode M n P),
    PerLetterIntegrabilityForConverse P N h_meas c ∧
    ContinuousMIChainRuleForConverse P N h_meas c ∧
    DPIForConverse P N h_meas c
```

### 必要 Mathlib API / Common2026 既存補題

- 姉妹 `IsAwgnRandomCodingFeasible` 構造を参考 (`AWGNAchievabilityDischarge.lean:834`)。
- `awgnChannel` / `AwgnCode` 既存定義 (`AWGN.lean:74-100`)。
- 後続 Phase B 在庫 (Phase 0 で確定)。

### Done 条件

- [ ] `AWGNConverseDischarge.lean` 新規作成、skeleton 全 sorry で type-check
- [ ] A-1 ~ A-4 完了、bundle 定義 + honesty docstring 完備
- [ ] `lake env lean Common2026/Shannon/AWGNConverseDischarge.lean` clean
      (Phase B/C は sorry 残し OK)
- [ ] 判断ログ #1 (bundle structure 確定) append

### proof-log

yes (`proof-log-awgn-converse-aux-phaseA.md`)。

### 工数感

~80-180 行、1 session。

### 失敗時 fallback

- bundle 内 sub-bound 数が 5 件以上に膨張 → 1 bundle ではなく 2 bundle に分割
  (`IsAwgnConverseFanoFeasible` + `IsAwgnConversePerLetterFeasible`)、判断ログで
  記録。
- bundle field の型が input law `uniformW` を抱える形に肥大 → uniformW は AWGN
  converse において常に `Measure.uniformDiscrete (Fin M)` で fixed なので、
  bundle predicate が `uniformW` を引数に取らず内部で固定する形に pivot。

---

## Phase B-Fano — Fano application via `fano_inequality_measure_theoretic` 📋

### スコープ

Cover-Thomas 9.1.2 step 1: `H(W | Ŵ) ≤ binEntropy(Pe) + Pe · log(M-1)` を AWGN code
の error probability `Pe = (1/M) ∑ errorProbAt m` に接続。Fano 補題は既存
`fano_inequality_measure_theoretic` (`Common2026/Fano/Measure.lean:226`) を
**`X := Fin M`, `Y := Fin n → ℝ`** で直接呼出 (X 側の `Fintype + MeasurableSingletonClass`
は `Fin M` で自動充足、Y 側は制約なし)。

- B-Fano-1 `H(W) = log M` for uniform W on `Fin M`
  (`entropy_uniform_eq_log_card` 系、Phase 0 判断 #2 で在庫確認)
- B-Fano-2 `H(W) = H(W | Ŵ) + I(W; Ŵ)` (entropy chain rule、Phase 0 判断 #2)
- B-Fano-3 errorProb 同値性 bridge: AWGN `Pe = (1/M) ∑ errorProbAt m` と
  Fano `errorProb μ Xs Yo decoder = μ {ω | Xs ω ≠ decoder (Yo ω)}` の同値
  (uniform W + deterministic encoder + measurable decoder)
- B-Fano-4 `fano_inequality_measure_theoretic` 直接呼出 (`hcard := hM`、`Xs := W`、
  `Yo := Y^n`、`decoder := c.decoder`)
- B-Fano-5 結合: `log M ≤ binEntropy(Pe) + Pe · log(M-1) + I(W; Ŵ)`

### 入出力型 (key)

```lean
/-- Cover-Thomas 9.1.2 step 1: Fano application for AWGN code。 -/
theorem awgn_fano_inequality
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (hM : 2 ≤ M) (c : AwgnCode M n P)
    (Pe : ℝ) (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1)
        + (jointMIWWhat c h_meas).toReal := by
  -- B-Fano-1 + B-Fano-2 + B-Fano-3 + B-Fano-4 + B-Fano-5 で組み立て
  sorry
```

`jointMIWWhat c h_meas : ℝ≥0∞` は `I(W; Ŵ)` の typed RV 形 (Phase 0 で
`mutualInfo` 既存 def を確認後に local 定義)。

### 必要 Mathlib API / Common2026 既存補題

- `fano_inequality_measure_theoretic` (`Common2026/Fano/Measure.lean:226`、verbatim 確認済)
- `entropy_uniform_eq_log_card` 系 (Phase 0 判断 #2 で在庫確認、不在なら local
  ~10-20 行)
- `mutualInfo_eq_entropy_sub_condEntropy` 系 (entropy chain rule、Phase 0 判断 #2)
- AWGN error probability bridge: `c.toCode.errorProbAt (awgnChannel N h_meas) m` と
  Fano `errorProb` の同値性 (~15-25 行手書き、Phase 0 で似た bridge の在庫確認)

### Done 条件

- [ ] B-Fano-1 ~ B-Fano-5 完了
- [ ] `awgn_fano_inequality` publish、0 sorry
- [ ] `lake env lean ...` clean

### proof-log

yes (`proof-log-awgn-converse-aux-phaseB-fano.md`)。

### 工数感

~60-150 行、1-1.5 session。

### 失敗時 fallback

- `Fintype.card (Fin M) = M` の型 cast plumbing (`(M : ℝ) - 1` vs
  `((Fintype.card (Fin M) : ℝ) - 1)`) で詰まる → `simpa [Fintype.card_fin]` で
  吸収、~5 行追加。
- error probability bridge が肥大 (40+ 行) → bridge 補題を Phase A の bundle に
  staged hyp として packing (T-FFC-2 拡張)、判断ログで記録。
- `H(W) = log M` for uniform W が Common2026 不在 → local proof
  (`entropy = ∑ negMulLog (1/M) = log M`、~15-20 行)。

---

## Phase B-DPI/chain — DPI + memoryless chain rule 📋

### スコープ

Cover-Thomas 9.1.2 step 2-3: `I(W; Ŵ) ≤ I(X^n; Y^n) ≤ ∑ I(X_i; Y_i)`。

- B-DPI-1 DPI `I(W; Ŵ) ≤ I(X^n; Y^n)` (W → X^n encoder deterministic、
  Y^n → Ŵ decoder measurable、Markov chain W - X^n - Y^n - Ŵ)
  - Phase 0 判断 #3 で在庫確認、不在なら bundle 内 staged hyp `DPIForConverse`
    を destructure
- B-chain-1 memoryless chain rule `I(X^n; Y^n) ≤ ∑ I(X_i; Y_i)` for AWGN
  channel (Y_i = X_i + Z_i、Z_i iid 𝒩(0, N))
  - Phase 0 判断 #4 で在庫確認、不在なら bundle 内 staged hyp
    `ContinuousMIChainRuleForConverse` を destructure

### 入出力型 (key)

```lean
/-- Cover-Thomas 9.1.2 step 2: data processing inequality for code's
information chain `W → X^n → Y^n → Ŵ`. -/
theorem awgn_dpi
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P)
    (h_dpi : DPIForConverse P N h_meas c) :
    (jointMIWWhat c h_meas).toReal ≤ (jointMIXnYn c h_meas).toReal := by
  sorry

/-- Cover-Thomas 9.1.2 step 3: memoryless channel chain rule. -/
theorem awgn_chain_rule
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P)
    (h_chain : ContinuousMIChainRuleForConverse P N h_meas c) :
    (jointMIXnYn c h_meas).toReal
      ≤ ∑ i : Fin n, (perLetterMI c h_meas i).toReal := by
  sorry
```

### 必要 Mathlib API / Common2026 既存補題

- `condMutualInfo_chain_rule_X_2var` (Common2026 既存、`Fintype α` 制約あり、
  schema 参考のみ — direct reuse は壁発動)
- `mutualInfo_le_mutualInfo_of_measurable` 系 DPI (Phase 0 で loogle)
- bundle 内 staged hyp `DPIForConverse` / `ContinuousMIChainRuleForConverse`
- AWGN-agnostic continuous chain rule (姉妹 `awgn-mi-decomp-plan.md` Phase 6 と相補、
  closure 後に staged hyp を本物に置換可能)

### Done 条件

- [ ] B-DPI-1 + B-chain-1 完了
- [ ] `awgn_dpi` / `awgn_chain_rule` publish、0 sorry (bundle hyp 経由)
- [ ] `lake env lean ...` clean

### proof-log

yes (`proof-log-awgn-converse-aux-phaseB-dpi-chain.md`)。

### 工数感

~80-250 行、1-2 session。

### 失敗時 fallback

- continuous MI chain rule の `Fintype α` 壁が想定より深い → 本 plan の bundle 内
  staged hyp に集約 (T-FFC-3 確定発動)、後続 plan
  `awgn-converse-chainrule-discharge-plan.md` で genuine discharge。
- DPI が Mathlib 不在で bundle 内 staged にも詰めにくい (DPI の hyp 自身が深い) →
  本 plan の bundle 内 staged を 1 つ追加 (T-FFC-3 拡張)、判断ログで記録。
- `mutualInfo` typed RV 形 vs `klDiv` 形の bridge mismatch (姉妹 mi-bridge plan の
  scope 重複) → 姉妹 `awgn-mi-bridge-plan.md` への dependency 明記、本 plan の本体は
  staged hyp 経由で進める。

---

## Phase B-Gaussian — per-letter `I(X_i; Y_i) ≤ (1/2) log(1+P/N)` 📋

### スコープ

Cover-Thomas 9.1.2 step 4: per-letter Gaussian max-entropy bound。

- B-Gauss-1 per-letter input power: `∑ (X_i)² ≤ nP` ⇒ `(1/n) ∑ E[X_i²] ≤ P` ⇒
  `∃ i, E[X_i²] ≤ P` … wait これは違う、**average power** で per-letter は
  `E[X_i²] ≤ P` を一律 derive (Cauchy-Schwarz は不要、power constraint は per-message
  `∑ᵢ (encoder m i)² ≤ nP` なので uniform W のもとで `E[X_i²] = (1/M) ∑ₘ (encoder m i)²`
  ⇒ `∑ᵢ E[X_i²] = (1/M) ∑ₘ ∑ᵢ (encoder m i)² ≤ (1/M) · M · nP = nP` ⇒ avg `E[X_i²] ≤ P`)
- B-Gauss-2 per-letter `Y_i` の law: `Y_i = X_i + Z_i`, `Z_i ∼ N(0, N)` indep ⇒
  `μ_{Y_i} = μ_{X_i} ∗ N(0, N)` (convolution、`gaussianReal_conv_gaussianReal` 系)
- B-Gauss-3 per-letter `Y_i` の variance: `E[Y_i²] = E[X_i²] + E[Z_i²] ≤ P + N`
  (independence of X_i, Z_i + `variance_id_gaussianReal`)
- B-Gauss-4 per-letter `h(Y_i)` Gaussian max-entropy:
  `differentialEntropy_le_gaussian_of_variance_le` を `μ := μ_{Y_i}`, `v := P+N` で
  起動。4 hypothesis のうち 3 (mean, var, var_int) は B-Gauss-1 ~ B-Gauss-3 から
  derive、4 つ目 `h_ent_int` は bundle 内 staged hyp `PerLetterIntegrabilityForConverse`
  から取得。
- B-Gauss-5 per-letter `h(Y_i | X_i) = h(Z_i)` (channel is AWGN、Y_i conditional on
  X_i is X_i + Z_i shifted、entropy shift-invariant + Z_i 独立 ⇒
  `h(Y_i | X_i) = h(Z_i) = (1/2) log(2πeN)` via `differentialEntropy_gaussianReal`)
- B-Gauss-6 per-letter `I(X_i; Y_i) = h(Y_i) - h(Y_i | X_i)` (textbook MI 形)
  — **F-2 bridge** (姉妹 `awgn-mi-bridge-plan.md` scope)。本 plan 内では F-2 既存
  hypothesis pass-through で取得 (`h_mi_bridge_per_letter`) — または `awgn-mi-decomp-plan.md`
  Phase 7 完了後に genuine discharge 可能。
- B-Gauss-7 結合: `I(X_i; Y_i) ≤ (1/2) log(2πe(P+N)) - (1/2) log(2πeN) =
  (1/2) log((P+N)/N) = (1/2) log(1 + P/N)` (`Real.log_div` + `Real.log_mul`)

### 入出力型 (key)

```lean
/-- Cover-Thomas 9.1.2 step 4: per-letter mutual information is bounded by
the Gaussian channel capacity. -/
theorem awgn_per_letter_mi_le_capacity
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P)
    (h_per_letter : PerLetterIntegrabilityForConverse P N h_meas c)
    (h_mi_bridge_per_letter :
        ∀ i : Fin n, (perLetterMI c h_meas i).toReal
          = differentialEntropy (perLetterYLaw c h_meas i)
            - differentialEntropy (gaussianReal 0 N))
    (i : Fin n) :
    (perLetterMI c h_meas i).toReal ≤ (1/2) * Real.log (1 + P / (N : ℝ)) := by
  sorry
```

### 必要 Mathlib API / Common2026 既存補題

- `differentialEntropy_le_gaussian_of_variance_le` (`Common2026/Shannon/DifferentialEntropy.lean:518`、verbatim 確認済)
- `differentialEntropy_gaussianReal` (`Common2026/Shannon/DifferentialEntropy.lean:412`、verbatim 確認済)
- `gaussianReal_conv_gaussianReal` (Mathlib `Real.lean:613`)
- `gaussianReal_add_gaussianReal_of_indepFun` (Mathlib `Real.lean:624`、typed RV 形)
- `variance_id_gaussianReal` / `integral_id_gaussianReal` (Mathlib)
- bundle 内 staged hyp `PerLetterIntegrabilityForConverse`
- F-2 MI bridge `mutualInfoOfChannel_gaussianInput_closed_form` (姉妹 plan、本 plan は
  per-letter local 形を hyp として pass-through、`awgn-mi-decomp-plan.md` Phase 7
  完了後に genuine 化)

### Done 条件

- [ ] B-Gauss-1 ~ B-Gauss-7 完了
- [ ] `awgn_per_letter_mi_le_capacity` publish、0 sorry (bundle hyp + F-2 hyp 経由)
- [ ] `lake env lean ...` clean

### proof-log

yes (`proof-log-awgn-converse-aux-phaseB-gaussian.md`)。

### 工数感

~120-250 行、1.5-2 session。

### 失敗時 fallback

- B-Gauss-2 per-letter Y_i law の convolution form が `gaussianReal_conv_gaussianReal`
  と shape mismatch (mean shift `Y_i = X_i + Z_i` で X_i は input distribution
  なので generic measure、Y_i 直接 closed-form Gaussian にならない) → Y_i 法を
  bundle hyp として packing (T-FFC-2 拡張) ⇒ honest "Mathlib gap" 維持。
- F-2 bridge per-letter 形が姉妹 `awgn-mi-bridge-plan.md` の bridge と shape mismatch
  → 本 plan 内で per-letter bridge を hyp 引数として外出し (姉妹 plan の bridge と
  parallel に保つ)、判断ログで記録。

---

## Phase C — `isAwgnConverseFeasible_discharger` 統合 + wrapper 📋

### スコープ

Phase B-Fano + B-DPI/chain + B-Gaussian を組み立てて主定理 publish。

- C-1 `isAwgnConverseFeasible_discharger` 本体: Fano + DPI + chain + per-letter
  bound + sum
  ```
  log M ≤ binEntropy(Pe) + Pe · log(M-1) + I(W; Ŵ)            -- B-Fano (B-Fano-5)
        ≤ binEntropy(Pe) + Pe · log(M-1) + I(X^n; Y^n)         -- B-DPI-1
        ≤ binEntropy(Pe) + Pe · log(M-1) + ∑ I(X_i; Y_i)       -- B-chain-1
        ≤ binEntropy(Pe) + Pe · log(M-1) + n · (1/2) log(1+P/N) -- B-Gauss-7 (sum)
  ```
- C-2 `awgn_converse_F3_discharged` wrapper: `awgn_converse` の `sorry` を
  `isAwgnConverseFeasible_discharger` 呼出に置換するための薄い wrapper
- C-3 `AWGNConverse.lean:70` の body 置換 (本 plan 完了時に orchestrator が実施 or
  本 file 内で本 plan の wrapper を import 経路で `awgn_converse` 自身を 1 行
  passthrough に書換 — 判断 #6 候補)

### Done 条件

- [ ] C-1 ~ C-3 publish
- [ ] `lake env lean Common2026/Shannon/AWGNConverseDischarge.lean` clean
      (0 sorry / 1 staged bundle hyp `IsAwgnConverseFeasible`)
- [ ] `lake env lean Common2026/Shannon/AWGNConverse.lean` clean
      (body `sorry` 解消、`isAwgnConverseFeasible_discharger` 呼出に置換)
- [ ] `Common2026.lean` に 1 行 import 追加 (Phase V でオーケストレータ実施)

### proof-log

no (skeleton 整地のため)。

### 工数感

~30-80 行、0.5-1 session。

### 失敗時 fallback

- 統合時に bundle destructure pattern が complex (姉妹 1641 行 E-1 body の `obtain` pattern 参考)
  → bundle field を `.fano` / `.dpi` / `.chain` / `.per_letter` の dot accessor 形に
  rename (`structure` 化)、destructure を簡潔化。
- `AWGNConverse.lean:70` の body 置換で signature mismatch (引数順序 / namespace
  解決) → wrapper 経由でなく本 file `AWGNConverseDischarge.lean` 内で
  `awgn_converse` を本物呼出に書換、`AWGNConverse.lean` 自身は無変更
  (orchestrator が `AWGNConverseDischarge.lean` を `Common2026.lean` に import 追加
  + 主定理 wrapper `AWGNMain.lean` の signature 更新)。

---

## Phase V — verify + Common2026.lean 編入準備 📋

### スコープ

最終 verify + honesty 再 audit + Common2026.lean 編入位置確定。

### Done 条件

- [ ] `lake env lean Common2026/Shannon/AWGNConverseDischarge.lean` silent
- [ ] `lake env lean Common2026/Shannon/AWGNConverse.lean` silent
      (body sorry 解消、`@residual(plan:awgn-converse-aux-plan)` → `@audit:staged(awgn-converse-feasible)` に降格)
- [ ] **独立 honesty audit subagent 起動** (CLAUDE.md「Independent honesty audit」必須):
      `IsAwgnConverseFeasible` bundle の 4 条件 verify
      (a) signature ≠ `awgn_converse` 結論、
      (b) Mathlib 壁 (per-letter integrability / chain rule / DPI) 明示、
      (c) `isAwgnConverseFeasible_discharger` body が genuine assembly (Phase B-Fano
          + B-DPI/chain + B-Gaussian の連鎖)、
      (d) `@audit:staged(awgn-converse-feasible)` タグ付与確認
- [ ] `Common2026.lean` に 1 行追加 (オーケストレータ実施):
      ```lean
      import Common2026.Shannon.AWGNConverseDischarge
      ```

### proof-log

no。

### 工数感

0.25 session。

---

## 撤退ライン

### Scope 縮小ライン (発動時に T2-A F-3 完成形を縮小)

- **T-FFC-1: Fano 適用時の `[StandardBorelSpace (Fin n → ℝ)]` 自動推論失敗**
  (Phase B-Fano、Fano Phase 3 経験で同様の事故あり)
  - 縮退案: `instance : StandardBorelSpace (Fin n → ℝ)` を本 file 内 local で
    derive (~10-20 行)、type-class plumbing を吸収。判断ログで記録。

- **T-FFC-2: per-letter integrability `h_ent_int` の Mathlib 壁** (Phase A、
  **最有力**)
  - 縮退案: bundle 内 `PerLetterIntegrabilityForConverse` staged hyp として packing
    (姉妹 `IsAwgnPowerConstraintHonest` と同型)。本 plan の bundle predicate の中心。
    closure は後続 plan `awgn-converse-feasible-discharge-plan.md` (まだ未起草) に
    委ねる。
  - **honesty 必須条件**: (a) 結論型と異なる、(b) docstring で "Mathlib gap, NOT
    load-bearing" 明記、(c) Phase B-Gaussian で本物 assembly、(d) `@audit:staged(awgn-converse-feasible)`
    タグ

- **T-FFC-3: continuous MI chain rule `I(X^n; Y^n) ≤ ∑ I(X_i; Y_i)` の Mathlib 壁**
  (Phase B-DPI/chain、確定発動見込み)
  - 縮退案: bundle 内 `ContinuousMIChainRuleForConverse` staged hyp として packing。
    姉妹 `awgn-mi-decomp-plan.md` Phase 6 一般 body 補題と相補 (同 plan が closure
    すれば本 staged hyp も自動 discharge 候補)。

- **T-FFC-4: 規模超過 (~1000 行超)** (Phase 全体、低確率)
  - 縮退案: 本 plan を 2 file に分割:
    - `AWGNConverseDischargeFano.lean` (Phase B-Fano + B-DPI、~250 行)
    - `AWGNConverseDischargePerletter.lean` (Phase B-chain + B-Gaussian + Phase C、~400 行)

### honesty 撤退ライン (常時)

本 plan の goal は `awgn_converse` body sorry を **analytic body** で埋めること。
以下の rebrand は本 plan の **失敗**:

- ❌ name laundering (`awgn_converse_full_discharged` 等の別名 passthrough を作って
  `IsAwgnConverseFeasible` を hyp なしに見せかける)
- ❌ `IsAwgnConverseFeasible` bundle 中身が conclusion-as-hypothesis
  (`log M ≤ n · C + binEntropy + …` を含む — `ContinuousMIChainRuleForConverse` の
  結論型は `I(X^n; Y^n) ≤ ∑ I(X_i; Y_i)` であり、`awgn_converse` 結論型と異なるか
  をひもづくレベルで保つ)
- ❌ Phase C の `isAwgnConverseFeasible_discharger` 本体が `h_feasible …` 1 行に
  縮退 (Phase B-Fano / B-DPI / B-chain / B-Gaussian が integrate されていない)

CLAUDE.md「検証の誠実性」tells、`scripts/audit_db.ts` 再 audit で機械的に検出。
姉妹 `awgn-achievability-typicality-plan.md` §「honesty 撤退ライン」と同型。

### load-bearing hypothesis 禁止規律 (判定軸明示)

CLAUDE.md「検証の誠実性」「load-bearing hypothesis bundling」の判定軸を本 plan に
適用する:

| 判定対象 | 判定 | 理由 |
|---|---|---|
| `IsAwgnConverseFeasible P N h_meas` (bundle predicate) | **regularity (Mathlib 壁 packaging)** | (a) bundle の結論型 ≠ `awgn_converse` 結論、(b) 3 sub-bound はそれぞれ Mathlib 壁 (per-letter integrability / continuous chain rule / DPI continuous) の analytic primitive を表現、(c) `isAwgnConverseFeasible_discharger` body が Fano + chain + per-letter で genuine assembly、(d) `@audit:staged` 付与で stage 表明 |
| `PerLetterIntegrabilityForConverse` (sub-bound 1) | **regularity (Mathlib 壁)** | per-letter `h_ent_int` Integrable は Mathlib 壁、結論型 `Integrable (negMulLog (rnDeriv ...)) volume` は `awgn_converse` 結論と無関係 |
| `ContinuousMIChainRuleForConverse` (sub-bound 2) | **regularity (Mathlib 壁)** | 結論型 `I(X^n;Y^n) ≤ ∑ I(X_i;Y_i)` は `awgn_converse` 結論 `log M ≤ n·C + binEntropy + …` と異なる、chain rule で分解した中間量 |
| `DPIForConverse` (sub-bound 3) | **regularity (Mathlib 壁)** | 結論型 `I(W;Ŵ) ≤ I(X^n;Y^n)` は `awgn_converse` 結論と異なる、DPI で分解した中間量 |
| 仮に `IsAwgnConverseClaim P N h_meas : Prop := ∀ M n c Pe, log M ≤ n·C + binEntropy + …` (禁止例) | **load-bearing (核 bundling、禁止)** | predicate 自身が結論型そのもの → CLAUDE.md「circular `:= h`」defect 同等、tier 5 |

本 plan の bundle は **regularity** 側に分類される。新規導入時は honesty 4 条件
全て満たすこと (4 条件 → §Goal / Approach の honesty 規律ブロック)。

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| **per-letter integrability `h_ent_int` の Mathlib 壁** (Phase B-Gauss-4) | **高** (確定発生想定) | **中** (bundle 内 staged hyp に集約) | T-FFC-2 staged 採用、後続 plan に discharge 委譲 |
| **continuous MI chain rule の Mathlib 壁** (Phase B-chain-1) | **高** (確定発生想定) | **中** (bundle 内 staged hyp) | T-FFC-3 staged 採用、姉妹 `awgn-mi-decomp-plan.md` Phase 6 と相補 |
| **DPI continuous の Mathlib 壁** (Phase B-DPI-1) | 中 (Common2026 在庫次第) | 中 (bundle 内 staged hyp 追加) | Phase 0 inventory で在庫確認、不在なら T-FFC-3 拡張 |
| **`fano_inequality_measure_theoretic` の `[StandardBorelSpace (Fin n → ℝ)]` 自動推論失敗** (Phase B-Fano-4) | 中 (Fano Phase 3 経験) | 低 (~10-20 行 plumbing) | T-FFC-1 local instance |
| **F-2 MI bridge per-letter 形 shape mismatch** (Phase B-Gauss-6) | 中 | 中 (本 plan 内 per-letter bridge hyp 追加 = +1 hyp、姉妹 plan と parallel) | 判断ログで記録、姉妹 `awgn-mi-bridge-plan.md` への dependency 明記 |
| **error probability bridge (AWGN `Pe` vs Fano `errorProb`) が肥大** (Phase B-Fano-3) | 中 | 中 (Phase B-Fano +25-50 行) | Phase 0 で類似 bridge の在庫確認、なければ手書きで吸収 |
| **per-letter input power 評価 (`E[X_i²] ≤ P` derivation) のplumbing 肥大** (Phase B-Gauss-1) | 低-中 | 低 (~20-30 行) | uniform W 上の average 計算で素直に出る、必要なら local 補題化 |
| **規模超過 (~1000 行超)** | 低-中 (中央予測 650 行、悲観 990 行) | 中 (T-FFC-4 で 2 file 分割) | Phase 0 規模再見積、超過確度高ければ事前 2 分割 |
| **honesty defect 混入** (bundle predicate が rebrand 化 / load-bearing 化) | 低 | **高** (plan goal 失う) | §「honesty 撤退ライン」3 条件 + §「load-bearing 禁止規律」判定軸、Phase V 独立 audit subagent 起動 |
| **`awgn-mi-decomp-plan.md` Phase 6 一般 body 補題との scope 重複 / 衝突** | 低 | 中 (本 plan の staged hyp と相補的) | 姉妹 plan の Phase 6 完了が先に来たら、本 plan の `ContinuousMIChainRuleForConverse` を staged から genuine に書換可能 — 判断ログで境界明示 |

---

## 親 plan / 兄弟 plan との scope 区別

| Plan | スコープ | 出力 | 状態 |
|---|---|---|---|
| `awgn-moonshot-plan.md` (親) | T2-A 全体 (capacity + achiev + converse + main) | AWGN.lean + 3 sibling | DONE (4 撤退ライン honest pass-through) |
| `awgn-achievability-typicality-plan.md` (兄弟、F-1) | achievability core (sphere packing / continuous AEP / random coding / expurgation) | AWGNAchievabilityDischarge.lean (1641 行) | DONE (3 staged hyp bundle、judgement #7 で 1 bundle に集約) |
| `awgn-mi-bridge-plan.md` (兄弟、F-2) | channel MI ↔ `h(Y) − h(Y|X)` 形 bridge | TBD | 起草中 (stub) |
| `awgn-mi-decomp-plan.md` (兄弟、F-2 deeper) | continuous channel MI chain rule (AWGN 非依存 body 補題) | AWGNMIDecompBody.lean ほか | 起草中 (Phase 0-V skeleton 済、Phase 1-8 未着手) |
| **本 plan** | **F-3** (Fano + DPI + chain + per-letter Gaussian max-entropy 連鎖) | AWGNConverseDischarge.lean (~650 行) | **起草中 (本 file)** |
| `awgn-f1-f3-peer-simultaneous-migration-plan.md` (兄弟、Round 4 escalate #1) | F-1/F-3 peer migration (predicate 削除 + Tier 2 sorry 化) | AWGNAchievability.lean (52) + AWGNConverse.lean (73) Tier 2 化 | DONE (2026-05-27 commit、本 plan の起点となる Tier 2 状態を作成) |
| `awgn-f1-discharge-moonshot-plan.md` (兄弟、F-4) | kernel measurability discharge | AWGNF1Discharge.lean (148) | DONE |

**重要**:

- 本 plan は `awgn-f1-f3-peer-simultaneous-migration-plan.md` の **出口 successor**
  (Tier 2 sorry を analytic body で埋める)。peer の F-1 側は姉妹
  `awgn-achievability-typicality-plan.md` (1641 行) が既に同等の役割を果たしている
  (現状 3 staged hyp 残置、`awgn_achievability` の sorry を embedded で消すには bundle
  consumer wrapper が必要)。本 plan は F-3 側のその対称形を作る。
- 本 plan の `IsAwgnConverseFeasible` の `ContinuousMIChainRuleForConverse`
  sub-bound は `awgn-mi-decomp-plan.md` Phase 6 と相補。同 plan が closure すれば
  本 staged hyp も自動 discharge 候補だが、scope は独立 (本 plan の bundle は
  converse 全体の packaging、`awgn-mi-decomp` は AWGN-agnostic body 補題)。
- 本 plan の Phase B-Gaussian の F-2 bridge per-letter 形は
  `awgn-mi-bridge-plan.md` / `awgn-mi-decomp-plan.md` のいずれかが closure すれば
  本 plan の hyp も自動 discharge 候補 (姉妹 plan への dependency)。

---

## オーケストレータ注記

- 実装 agent は `Common2026.lean` を編集しない (Phase V でオーケストレータが 1 行追加)
- 実装 agent はコミットしない (Phase 単位で orchestrator が commit + push)
- **Phase 0 で判断 #1-#5 を確定**してから Phase A 着手。判断ログ #1 必須
- **Phase A 完了後、独立 honesty audit subagent 必須起動** (CLAUDE.md「Independent
  honesty audit」: 新規 `sorry` + `@residual` 導入 commit + 新規 staged predicate
  導入 commit のため必須)。bundle predicate の 4 条件 verify を auditor に依頼。
- **Phase B-Fano が最初の山場**。`fano_inequality_measure_theoretic` の verbatim 確認は
  起草前に済んでいるが、`X := Fin M`, `Y := Fin n → ℝ` substitution での type-class
  整合は Phase B-Fano 着手時に再 verbatim 確認。
- **Phase B-chain が最大の山場**。Mathlib 壁 `ContinuousMIChainRuleForConverse` は
  staged で確定見込み、姉妹 `awgn-mi-decomp-plan.md` Phase 6 完了状態によっては
  genuine discharge に書換可能。
- Phase 単位 proof-log は実装 agent が `docs/shannon/` 直下に append
  (Phase A-B: yes、Phase C/V: no)
- **honesty 再 audit**: Phase V で `scripts/audit_db.ts` 等で bundle predicate が
  regularity 判定されることを確認。defect 混入時は §「honesty 撤退ライン」「load-bearing
  禁止規律」に従い再起草

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### #0 (2026-05-27) plan 起草 — peer migration 出口 successor として本 plan 確定

`awgn-f1-f3-peer-simultaneous-migration-plan.md` (Round 4 escalate #1) により
2026-05-27 に F-1/F-3 peer 同時第一選択 migration が commit され、
`Common2026/Shannon/AWGNConverse.lean:59-70` の `awgn_converse` body は
`sorry + @residual(plan:awgn-converse-aux-plan)` の Tier 2 状態。
本 plan の責務はその analytic body 完成に絞られる。

本 plan は **姉妹 `awgn-achievability-typicality-plan.md` (1641 行、3 staged hyp
bundle) と対称な structure** を採用する:

- 姉妹 = achievability core (sphere packing + random coding + expurgation) + 3
  Mathlib 壁 (continuous SMB / n-d differentialEntropy / chi-square SLLN) を 1
  bundle `IsAwgnRandomCodingFeasible` に集約 (judgement #7、commits `9dcef00`
  → `2ace40b` → `c02304c`)
- 本 plan = converse core (Fano + DPI + chain + per-letter Gaussian max-entropy)
  + 3 Mathlib 壁 (per-letter integrability / continuous MI chain rule / DPI
  continuous) を 1 bundle `IsAwgnConverseFeasible` に集約 (T-FFC-2 + T-FFC-3 +
  Phase 0 判断 #3)

姉妹の 1641 行に対し converse は randomization 工程不在で **~650 行** 中央予測。

### #1 (TBD、Phase 0 完了時) inventory + bundle structure 確定

5 軸 inventory 完了後、bundle 内 sub-bound 数 (2/3/4)、witness 必要性
(姉妹 `∃ P'` 形が converse でも必要かどうか)、各 sub-bound の field 型を確定。

採否確定予定の項目 (Phase 0 終了時 append):

- (a) bundle field 数 = 3 (per-letter integrability + chain rule + DPI) or
      bundle field 数 = 4 (above + entropy chain rule for `H(W) = H(W|Ŵ) + I(W;Ŵ)`)
- (b) witness の有無 (姉妹 `∃ P'` は achievability codebook variance 緩和 slack のため、
      converse 側は input law が code 由来でコードブック非依存 → witness 不要が見込み)
- (c) DPI continuous の Common2026 在庫判定 (在庫あれば genuine、不在なら bundle に格納)
- (d) entropy chain rule + uniform W 在庫判定 (Phase B-Fano の前提)
- (e) 規模再見積 (Phase 0 inventory の Mathlib 壁判定数によって ~400-990 行 spread)

### #2 (TBD、Phase A 完了時) bundle predicate `IsAwgnConverseFeasible` 確定形

Phase 0 判断 #1 を受けて bundle 確定形を append、独立 honesty audit subagent verdict
(`load_bearing_hyp / honest` 期待) を併記。

### #3 (TBD、Phase B-Fano 完了時) Fano application 完了 + Type class 整合確認

`fano_inequality_measure_theoretic` を `X := Fin M, Y := Fin n → ℝ` で起動した
結果、T-FFC-1 (`[StandardBorelSpace (Fin n → ℝ)]`) が発動したか / local instance
で吸収できたかを記録。

### #4 (TBD、Phase B-DPI/chain 完了時) DPI + chain rule の壁発動状況

bundle 内 staged hyp `DPIForConverse` と `ContinuousMIChainRuleForConverse` の
それぞれが「Mathlib 壁の staged」「Common2026 在庫の genuine 化」のいずれに着地
したかを記録。

### #5 (TBD、Phase B-Gaussian 完了時) F-2 bridge per-letter 形の処理

姉妹 `awgn-mi-bridge-plan.md` / `awgn-mi-decomp-plan.md` の F-2 bridge per-letter
形と shape 整合したか、本 plan 内で追加 hyp 引数として外出ししたかを記録。

### #6 (TBD、Phase C 完了時) `AWGNConverse.lean:70` の body 置換ルート

`AWGNConverse.lean` 自身を `awgn_converse_F3_discharged` 呼出に書換るルート
(judgement #6-A) と、`AWGNConverseDischarge.lean` 内で independent wrapper を作り
`AWGNConverse.lean` は無変更にするルート (judgement #6-B) のいずれを採用したかを記録。

### #7 (TBD、Phase V 完了時) 規模実績 + honesty audit verdict

実績 LOC + 0 sorry / staged hyp 数 + 独立 honesty audit verdict
(`load_bearing_hyp / honest 🟢ʰ` 期待) + `@audit:staged(awgn-converse-feasible)`
タグ整合確認。本 plan 完了で `awgn_converse` body sorry は解消、staged hyp 1 本
(`IsAwgnConverseFeasible`) が残置 → 後続 plan
`awgn-converse-feasible-discharge-plan.md` (まだ未起草) に委ねる。
