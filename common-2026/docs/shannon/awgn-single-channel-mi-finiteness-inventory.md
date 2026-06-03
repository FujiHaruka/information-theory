# AWGN single-channel MI finiteness (`klDiv ≠ ⊤`) — Mathlib/InformationTheory 在庫 + 独立 wall 再検証

> 親計画: `docs/shannon/parallel-gaussian-l-pg1-discharge-plan.md`（step 5 が finiteness を own）。
> 対象 residual: `InformationTheory/Draft/Shannon/ParallelGaussianPerCoord.lean:717` の
> `awgn_mutualInfoOfChannel_ne_top`（唯一の active sorry、`@residual(plan:parallel-gaussian-l-pg1-discharge-plan)`）。
> handoff（2026-05-29）の指示通り「loogle Found 0 を鵜呑みにせず独立 wall 再検証」を実施。

---

## 一行サマリ

**判定: self-buildable（中央見積 ~50-90 行）。真の壁ではない。** finiteness `klDiv ≠ ⊤` は
`klDiv_ne_top_iff`（型クラス前提**ゼロ**）で AC + llr integrability に分解される。AC は
`ContChannelMIDecomp.lean:556-559` で**既に genuine 構築済み**、llr integrability の
analytic core（fibre log-density joint integrability `integrable_log_proxy_fibre_compProd`、
output log-density integrability `integrable_log_rnDeriv_gaussianReal`、llr の Bayes split
`llr_compProd_prod_split`）も**すべて既存 genuine 補題として `ContChannelMIDecomp.lean` に在庫**。
残作業は「既存 split + 2 個の既存 integrability を `.sub` + `Integrable.congr` で組んで
`klDiv_ne_top` に渡す」糊コードのみ。**唯一の genuine な未解決は退化 `N = 0`**（決定論 channel、
proxy-density route が breaks）で、target signature に `N ≠ 0` が無いため別 branch が要る（~15 行）。

- 既存率（finiteness に使う API 実体ベース）: **~90%**（AC + 2 integrability + split + `klDiv_ne_top` 全部既存）
- 自作必要: **2 件**（(1) llr integrability の組み立て補題、(2) `N = 0` 退化 branch）
- 撤退ライン発動: **No**（親 plan の step 5「軽 ~15-25 行」見積は llr-integrability obligation を
  underweight しているが、analytic core が既存のため真の壁化はしない。step 5 の工数を ~50-90 行に
  上方修正するだけで足りる）

---

## 主定理の最終形（residual signature 再掲）

`InformationTheory/Draft/Shannon/ParallelGaussianPerCoord.lean:717-720`（verbatim）:

```lean
theorem awgn_mutualInfoOfChannel_ne_top (N : ℝ≥0)
    (h_meas : InformationTheory.Shannon.AWGN.IsAwgnChannelMeasurable N) (P : ℝ≥0) :
    mutualInfoOfChannel (gaussianReal 0 P) (awgnChannel N h_meas) ≠ ⊤ := by
  sorry
```

注意（verbatim 確認済）:
- 入力分散は `P : ℝ≥0`（`gaussianReal 0 P`、`P.toNNReal` ではない直接形）。
- `N ≠ 0` / `0 < P` の**仮定が無い**。退化 case（`P = 0` の Dirac 入力、`N = 0` の決定論 channel）
  を両方 cover する必要がある。
- `mutualInfoOfChannel p W := klDiv (jointDistribution p W) (p.prod (outputDistribution p W))`
  （`ChannelCoding.lean:85`、verbatim 確認済）。
  `jointDistribution p W = p ⊗ₘ W`（`:55`）、`outputDistribution p W = (p ⊗ₘ W).snd`（`:72`）。

証明戦略（pseudo-Lean、`N ≠ 0` の主 branch）:

```lean
-- p := gaussianReal 0 P, W := awgnChannel N h_meas, q := outputDistribution p W
rw [mutualInfoOfChannel, jointDistribution_def]
apply klDiv_ne_top
· -- AC: p ⊗ₘ W ≪ p.prod q                    [ContChannelMIDecomp.lean:556-559 と同型]
  rw [show p.prod q = p ⊗ₘ Kernel.const ℝ q from (Measure.compProd_const).symm]
  exact Measure.absolutelyContinuous_compProd_right_iff.mpr
          (ae_of_all _ fun x => (hWx_q x))   -- hWx_q : W x ≪ q (Gaussian全支持)
· -- Integrable (llr (p⊗ₘW) (p.prod q)) (p⊗ₘW)
  refine (Integrable.congr ?_ (llr_compProd_prod_split q hWx_q hq_vol h_joint_ac g hg_meas hg_ae).symm)
  -- llr =ᵐ log(g z).toReal - log(q.rnDeriv vol z.2).toReal
  exact (integrable_log_proxy_fibre_compProd P N hN h_meas).sub
          (h_int_out_joint)  -- = integrable_log_rnDeriv_gaussianReal at q, via snd
```

`q = gaussianReal 0 (P+N)`（`IsAwgnOutputGaussian` = Gaussian 畳み込み）。`N = 0` 退化は別 branch
（下記 §E）。

---

## A. `klDiv_ne_top` / `klDiv_ne_top_iff` の verbatim signature

`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`。
section 変数（`:53`）: `{α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}`。
**型クラス前提は section レベルにもこの 2 lemma 個別にも一切無い**（`[IsFiniteMeasure]` 等不要）。

| 概念 | file:line | verbatim signature | 結論形 |
|---|---|---|---|
| `klDiv` 定義 | `Basic.lean:57` | `noncomputable irreducible_def klDiv (μ ν : Measure α) : ℝ≥0∞ := if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ) else ∞` | `ℝ≥0∞` |
| `klDiv_ne_top` | `Basic.lean:103` | `lemma klDiv_ne_top (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : klDiv μ ν ≠ ∞` | `klDiv μ ν ≠ ∞` |
| `klDiv_ne_top_iff` | `Basic.lean:100` | `lemma klDiv_ne_top_iff : klDiv μ ν ≠ ∞ ↔ μ ≪ ν ∧ Integrable (llr μ ν) μ` | `klDiv μ ν ≠ ∞ ↔ μ ≪ ν ∧ Integrable (llr μ ν) μ` |

**この事実が決定的**: finiteness は他に何の regularity も要求せず、AC と llr integrability の
2 点に**完全に**帰着する。`[IsFiniteMeasure]` / `[StandardBorelSpace]` 等の隠れた前提が無い。

---

## B. AC `jointDistribution ≪ prod marginals` の連続版 route — **既存 genuine**

joint = `p ⊗ₘ W`、prod marginals = `p.prod q`（`q := (p ⊗ₘ W).snd`）。
`p.prod q = p ⊗ₘ (Kernel.const ℝ q)`（`compProd_const`）なので、`compProd_right_iff` で
fibre-wise AC `∀ᵐ x ∂p, W x ≪ q` に帰着する。

### Mathlib 一般補題

| 概念 | file:line | verbatim signature | 結論形 |
|---|---|---|---|
| prod = compProd-const | `Probability/Kernel/Composition/MeasureCompProd.lean:141` | `lemma compProd_const {ν : Measure β} [SFinite μ] [SFinite ν] : μ ⊗ₘ (Kernel.const α ν) = μ.prod ν` | `μ ⊗ₘ Kernel.const α ν = μ.prod ν` |
| compProd-right AC iff | `Probability/Kernel/Composition/AbsolutelyContinuous.lean:86` | `lemma absolutelyContinuous_compProd_right_iff [SFinite μ] : μ ⊗ₘ κ ≪ μ ⊗ₘ η ↔ ∀ᵐ a ∂μ, κ a ≪ η a` | `μ ⊗ₘ κ ≪ μ ⊗ₘ η ↔ ∀ᵐ a ∂μ, κ a ≪ η a` |
| compProd-right AC (mp 向き) | `MeasureCompProd.lean:266` | `lemma AbsolutelyContinuous.compProd_right [SFinite μ] [IsSFiniteKernel η] (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) : μ ⊗ₘ κ ≪ μ ⊗ₘ η` | `μ ⊗ₘ κ ≪ μ ⊗ₘ η` |
| Gaussian ≪ volume | `Probability/Distributions/Gaussian/Real.lean:228` | `lemma gaussianReal_absolutelyContinuous (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : gaussianReal μ v ≪ volume` | `gaussianReal μ v ≪ volume` |
| volume ≪ Gaussian | `Real.lean:233` | `lemma gaussianReal_absolutelyContinuous' (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : volume ≪ gaussianReal μ v` | `volume ≪ gaussianReal μ v` |

`compProd_right_iff` の前提は `[SFinite μ]` のみ（probability measure → SFinite 自動）。
`AbsolutelyContinuous.compProd_right` は追加で `[IsSFiniteKernel η]`（`Kernel.const _ q`、`q` finite → OK）。

### InformationTheory 既存補題（fibre-vs-output AC + joint AC が genuine 構築済み）

| 概念 | file:line | verbatim signature | 結論形 |
|---|---|---|---|
| fibre ≪ output（Gaussian合成） | `InformationTheory/Draft/Shannon/ContChannelMIDecomp.lean:353` | `theorem awgnChannel_apply_absolutelyContinuous_output (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0) (hPN : P.toNNReal + N ≠ 0) (h_meas : IsAwgnChannelMeasurable N) (h_out : IsAwgnOutputGaussian P N h_meas) (x : ℝ) : (awgnChannel N h_meas) x ≪ outputDistribution (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)` | `(awgnChannel N h_meas) x ≪ outputDistribution ...` |
| fibre ≪ volume | `InformationTheory/Shannon/AWGNMIDecompBody.lean:103` | `theorem awgnChannel_apply_absolutelyContinuous (N : ℝ≥0) (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N) (x : ℝ) : (awgnChannel N h_meas) x ≪ volume` | `(awgnChannel N h_meas) x ≪ volume` |
| output ≪ volume | `AWGNMIDecompBody.lean:114` | `theorem awgn_output_absolutelyContinuous_of_outputGaussian (P : ℝ) (N : ℝ≥0) (hPN : P.toNNReal + N ≠ 0) (h_meas : IsAwgnChannelMeasurable N) (h_out : IsAwgnOutputGaussian P N h_meas) : (outputDistribution (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)) ≪ volume` | `outputDistribution ... ≪ volume` |
| **joint AC（inline 構築済）** | `ContChannelMIDecomp.lean:556-559`（`isContChannelMIDecompHyp_awgn` 内 `have h_joint_ac`） | `(p ⊗ₘ W) ≪ p.prod q` を `compProd_const.symm` + `absolutelyContinuous_compProd_right_iff.mpr (ae_of_all _ hWx_q)` で構築 | `(p ⊗ₘ W) ≪ p.prod q` |

**結論（B）**: AC route は新規 analytic content ゼロ。既存補題の組み合わせ（または
`ContChannelMIDecomp.lean:556-559` のコピー）で得られる。fibre-vs-output AC は
`gaussianReal x N ≪ volume ≪ gaussianReal 0 (P+N)`（両 Gaussian 全支持）。

---

## C. llr integrability の連続版 route — **analytic core は既存 genuine、組み立てのみ自作**

`Integrable (llr (p ⊗ₘ W) (p.prod q)) (p ⊗ₘ W)`。
llr を Bayes split で「fibre log-density − output log-density」に書き換え、各項の既存
integrability を `.sub` で合成する。**Gaussian の二次形式 log-density の integrability
（genuine analytic content）は既に書かれている。**

### llr の split（既存）

| 概念 | file:line | verbatim signature | 結論形 |
|---|---|---|---|
| **joint llr の Bayes split** | `ContChannelMIDecomp.lean:206` | `theorem llr_compProd_prod_split (q : Measure ℝ) [IsProbabilityMeasure q] (hWx_q : ∀ x, W x ≪ q) (hq_vol : q ≪ volume) (h_joint_ac : (p ⊗ₘ W) ≪ p.prod q) (g : ℝ × ℝ → ℝ≥0∞) (hg_meas : Measurable g) (hg_ae : ∀ x, (fun y => (W x).rnDeriv volume y) =ᵐ[W x] fun y => g (x, y)) : (fun z => llr (p ⊗ₘ W) (p.prod q) z) =ᵐ[p ⊗ₘ W] (fun z => Real.log (g z).toReal - Real.log (q.rnDeriv volume z.2).toReal)` | `llr (p⊗ₘW) (p.prod q) =ᵐ[p⊗ₘW] log(g z).toReal − log(q.rnDeriv vol z.2).toReal` |

（section 変数: `{p : Measure ℝ} [IsProbabilityMeasure p] {W : Channel ℝ ℝ} [IsMarkovKernel W]` — `ContChannelMIDecomp.lean` の generic section ヘッダ。要 Read 1 回で確認、上記 signature の `[...]` は当該 section 由来）

### 各項の integrability（既存 genuine）

| 概念 | file:line | verbatim signature | 結論形 |
|---|---|---|---|
| **fibre log-density × joint integrable** | `ContChannelMIDecomp.lean:460` | `theorem integrable_log_proxy_fibre_compProd (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N) : Integrable (fun z : ℝ × ℝ => Real.log (gaussianPDF z.1 N z.2).toReal) ((gaussianReal 0 P.toNNReal) ⊗ₘ (awgnChannel N h_meas))` | `Integrable (fun z => log (gaussianPDF z.1 N z.2).toReal) (p ⊗ₘ W)` |
| output log-density × Gaussian integrable | `ContChannelMIDecomp.lean:423` | `theorem integrable_log_rnDeriv_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : Integrable (fun y => Real.log ((gaussianReal m v).rnDeriv volume y).toReal) (gaussianReal m v)` | `Integrable (fun y => log ((gaussianReal m v).rnDeriv vol y).toReal) (gaussianReal m v)` |
| log Gaussian pdf integrable | `ContChannelMIDecomp.lean:404` | `theorem integrable_log_gaussianPDFReal_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (m' : ℝ) (v' : ℝ≥0) : Integrable (fun y => Real.log (gaussianPDFReal m v y)) (gaussianReal m' v')` | `Integrable (fun y => log (gaussianPDFReal m v y)) (gaussianReal m' v')` |
| 二次形式 integrable | `ContChannelMIDecomp.lean:387` | `theorem integrable_sq_sub_gaussianReal (m m' : ℝ) (v' : ℝ≥0) : Integrable (fun y => (y - m) ^ 2) (gaussianReal m' v')` | `Integrable (fun y => (y - m)^2) (gaussianReal m' v')` |
| 二次形式 joint compProd integrable | `ContChannelMIDecomp.lean:477`（`integrable_log_proxy_fibre_compProd` 内 `have h_sq`） | `Integrable (fun z : ℝ × ℝ => (z.2 - z.1) ^ 2) (p ⊗ₘ W)`（`Measure.integrable_compProd_iff` 経由） | `Integrable (fun z => (z.2 − z.1)^2) (p ⊗ₘ W)` |

### InformationTheory 既存 KL closed-form（finiteness は出さないが llr 構造の参照点）

| 概念 | file:line | 注意 |
|---|---|---|
| 2-Gaussian KL closed form | `InformationTheory/Shannon/DifferentialEntropy.lean:672` `klDiv_gaussianReal_gaussianReal_eq` | `.toReal` 形（`toReal_klDiv_of_measure_eq` 使用、**`ne_top` を establish しない**）。ただし証明 body 内に `h_int_log_g₁`/`h_int_log_g₂`（log pdf の integrability、`DifferentialEntropy.lean:822,827`）が既にあり、これは単一 Gaussian-pair の llr integrability そのもの。joint 版は §C 上段の `ContChannelMIDecomp` 補題が担当。 |

### Mathlib に**無い**もの（loogle 確認）

- `Integrable (llr (gaussian) (gaussian)) (gaussian)` の専用 lemma:
  `Found 0`（`MeasureTheory.Integrable (MeasureTheory.llr _ _) _` 検索 28 件中、Gaussian 専用は皆無）。
- 条件付き KL の **fibre 積分形** `klDiv (p ⊗ₘ κ) (p ⊗ₘ η) = ∫ x, klDiv (κ x) (η x) ∂p`:
  **Mathlib 不在**（`ChainRule.lean` 冒頭 TODO「Add a version of the chain rule for the integral
  form of the conditional KL divergence」が明示。loogle
  `InformationTheory.klDiv, Measure.compProd, lintegral` = `Found 0`）。
  → だが finiteness にこの fibre 積分形は**不要**。`klDiv_ne_top_iff` の直接 llr integrability で済む。

**結論（C）**: llr integrability の genuine analytic content（Gaussian 二次形式 log-density の
joint/marginal integrability）は**すべて `ContChannelMIDecomp.lean` に既存**。新規作業は
「`llr_compProd_prod_split` で書き換え → fibre 項（`integrable_log_proxy_fibre_compProd`）
− output 項（`integrable_log_rnDeriv_gaussianReal` を `z.2` 経由で joint に lift）を `.sub`」
の組み立て補題 1 本（output 項の joint への lift は `ContChannelMIDecomp.lean:525-527` の
`h_int_out_joint` 構築パターンを再利用）。

---

## 主要前提条件ボックス（事故りやすい lemma の前提）

- **`klDiv_ne_top` (`Basic.lean:103`)**: measure に型クラス前提**ゼロ**。`hμν : μ ≪ ν` と
  `h_int : Integrable (llr μ ν) μ` の 2 つだけ。隠れた `[IsFiniteMeasure]` は無い。
- **`absolutelyContinuous_compProd_right_iff` (`AbsolutelyContinuous.lean:86`)**: `[SFinite μ]` 必須。
  `p = gaussianReal 0 P` は probability → SFinite 自動。`η = Kernel.const ℝ q`（mp 向き使うなら
  `[IsSFiniteKernel η]` も）。
- **`gaussianReal_absolutelyContinuous` / `'` (`Real.lean:228,233`)**: 両方 `hv : v ≠ 0` 必須。
  fibre AC で `N ≠ 0`、output `volume ≪ gaussianReal 0 (P+N)` で `P+N ≠ 0` が要る。
  → **退化 `N = 0` でここが崩れる**（§E）。
- **`llr_compProd_prod_split` (`ContChannelMIDecomp.lean:206`)**: `[IsProbabilityMeasure q]` +
  `hWx_q : ∀ x, W x ≪ q` + `hq_vol : q ≪ volume` + joint AC + 全支持 proxy `g` + a.e. bridge `hg_ae`。
  これらは AWGN では `N ≠ 0`, `P+N ≠ 0` 前提下で `isContChannelMIDecompHyp_awgn:540-559` が全部供給済み。
- **`integrable_log_proxy_fibre_compProd` (`ContChannelMIDecomp.lean:460`)**: `hN : N ≠ 0` 必須。
- **`IsAwgnOutputGaussian`（output = `gaussianReal 0 (P+N)`）**: これは別 file
  (`AWGNMIBridgeDischarge`) で discharge 済（`awgn_output_gaussian_of_bind_eq_conv`）。
  finiteness では output が **何であれ** AC さえ立てば良いが、proxy-density route は output が
  Gaussian であることに依存（`integrable_log_rnDeriv_gaussianReal` を q に適用）。

---

## D. 規模見積もり（3 段階）

| route | 楽観 | 中央 | 悲観 |
|---|---|---|---|
| AC `p⊗ₘW ≪ p.prod q` | 既存 inline コピー ~6 行 | ~10 行 | 独立補題化 ~20 行 |
| llr integrability（split + 2項 `.sub`） | ~25 行 | ~50 行 | ~80 行（output 項の joint lift で `integrable_compProd_iff` 再展開要） |
| `N = 0` 退化 branch | ~10 行 | ~15 行 | ~30 行（決定論 channel の klDiv=0 / dirac AC を別途） |
| **合計** | **~40 行** | **~75 行** | **~130 行** |

**判定: self-buildable（中央 ~75 行）**。前回の subadditivity（13 行）/ multivariate-mi（~150 行）
の中間。真の壁（Mathlib core 不在 + 自作 200 行超）には**該当しない** — analytic core が
`ContChannelMIDecomp.lean` に既存だから。親 plan step 5 の「軽 ~15-25 行」は AC のみを見て
llr integrability を見落とした過小見積。**~75 行に上方修正**すれば足りる。

---

## E. 退化境界の扱い（verbatim 確認済）

`gaussianReal μ 0 = Measure.dirac μ`（`Real.lean:207` verbatim 確認）。

| case | 入力 p | output q | joint | finiteness route |
|---|---|---|---|---|
| `P > 0, N ≠ 0`（主） | `gaussianReal 0 P`（全支持） | `gaussianReal 0 (P+N)`（全支持） | density あり | §B+C の主 route がそのまま通る。退化定義悪用なし genuine。 |
| `P = 0, N ≠ 0` | `gaussianReal 0 0 = dirac 0` | `(dirac 0 ⊗ₘ W).snd = W 0 = gaussianReal 0 N`（全支持、`P+N=N≠0`） | `dirac 0 ⊗ₘ W` | AC: `compProd_right_iff` の `∀ᵐ x ∂(dirac 0), W x ≪ q` は x=0 のみ要求、`W 0 = gaussianReal 0 N ≪ gaussianReal 0 N = q` で trivially 成立。llr integrability も `integrable_log_proxy_fibre_compProd`（`hN : N ≠ 0` のみ要求、P には `0 ≤` 不要、`P.toNNReal` も `P:ℝ≥0` 直接で OK）が通る。**P=0 でも genuine に通る。** |
| `N = 0`（任意 P）| 任意 | `gaussianReal x 0 = dirac x`、q = `dirac`（射影）| dirac-joint | **proxy-density route が breaks**（`gaussianReal_absolutelyContinuous N=0` で `hv : N≠0` 不成立）。channel は決定論（`W x = dirac x`）。joint `p ⊗ₘ (x↦dirac x)` は graph 上の measure、`p.prod q` は `dirac` の積。**MI = 0**（決定論 channel）で finite だが、**別 branch 要**（~15 行）。 |

**重要（degenerate-definition exploitation 回避）**: 主 route（P>0,N≠0）は退化を突かない genuine。
`P = 0` は専用退化処理を要さず主 route が自然に cover（CLAUDE.md の「退化定義悪用」に該当しない）。
**唯一の追加 branch は `N = 0`**。これは target signature が `N ≠ 0` を取らないことに起因する
genuine な edge であり、`@residual` で隠すのではなく `N = 0` で `klDiv (dirac-based joint) (dirac
prod) ≠ ⊤` を別途立てる（決定論 → finite measure 間の klDiv、`klDiv_ne_top_iff` の AC は graph
measure ≪ product が必要 — ここは小さいが要検討。最悪 `by_cases hN : N = 0` で `N=0` 側を
独立に処理）。

**注意（親 plan / handoff との整合）**: handoff は `awgn_mutualInfoOfChannel_ne_top` を
「llr integrability is genuine analytic content（same family as AWGN MI density work）」と
評価し「dedicated wall への promotion を merit するかも」と書くが、**本再検証の結論は逆**:
その density work は既に `ContChannelMIDecomp.lean` で genuine（0 sorry）に書かれており、
finiteness はそれを再利用する糊で済む。**promotion 不要、wall 化しない。**

---

## Mathlib 壁の列挙（真に不在のもの）

| 概念 | loogle 確認 | finiteness への影響 |
|---|---|---|
| 条件付き KL の fibre 積分形 `klDiv (p⊗ₘκ)(p⊗ₘη) = ∫ klDiv (κ x)(η x) ∂p` | `Found 0`（`ChainRule.lean` 冒頭 TODO 明示） | **finiteness には不要**。`klDiv_ne_top_iff` 直接 route で回避。値計算には欲しいが本タスク対象外。 |
| `Integrable (llr (gaussian)(gaussian)) (gaussian)` 専用 lemma | `Found 0` | InformationTheory が `ContChannelMIDecomp.lean` で genuine に構築済（壁ではない、self-built 済み）。 |
| compProd fibre rnDeriv（`(p⊗ₘκ).rnDeriv (p⊗ₘη) z =ᵐ κ.rnDeriv η z.1 z.2`） | Mathlib `Composition/RadonNikodym.lean:28-29` TODO | InformationTheory `ContChannelMIDecomp.lean:142` `rnDeriv_compProd_fibre` で genuine 構築済（壁ではない）。 |

→ **真の Mathlib 壁（`@residual(wall:...)` 対象）は本 finiteness タスクには存在しない。**
shared sorry 補題化候補も無し（既存 genuine 補題の再利用で閉じる）。

---

## 撤退ラインへの距離

親 plan `parallel-gaussian-l-pg1-discharge-plan.md` step 5（finiteness を own）の撤退ライン:
- step 5 は「軽 ~15-25 行」見積。**この見積は llr integrability obligation を underweight** している
  （handoff 自認）。

**判定: 撤退ライン発動しない。**
- finiteness は self-buildable（中央 ~75 行）。Mathlib core 不在も真の壁も無い。
- 縮退案は不要。**step 5 の工数見積を ~15-25 行 → ~50-90 行 に上方修正**するのが唯一の plan 更新。
- 退化 `N = 0` branch（~15 行）を step 5 のサブタスクに明記する（target が `N≠0` を取らないため）。

新規撤退ライン提案（保険、発動は想定せず）:
- **finiteness 着手後、`integrable_log_proxy_fibre_compProd` の output-項 joint lift が
  `integrable_compProd_iff` 再展開で 80 行超に膨れた場合** → output 項を
  `ContChannelMIDecomp.lean` 内に専用補題 `integrable_log_output_density_compProd` として
  括り出し（~30 行）、finiteness 本体はそれを呼ぶだけにする。これは縮退ではなく
  リファクタ（sorry 不要、`@residual` 不要）。

---

## 着手 skeleton

`InformationTheory/Draft/Shannon/ParallelGaussianPerCoord.lean:717` の sorry を埋める形（新規 file 不要、
analytic core を `ContChannelMIDecomp.lean` から import）。退化を `by_cases hN` で分ける skeleton:

```lean
-- ParallelGaussianPerCoord.lean の awgn_mutualInfoOfChannel_ne_top を置換
open MeasureTheory ProbabilityTheory InformationTheory
open InformationTheory.Shannon.ChannelCoding
open InformationTheory.Shannon.AWGN  -- llr_compProd_prod_split, integrable_log_*, awgn_* AC 補題

theorem awgn_mutualInfoOfChannel_ne_top (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) (P : ℝ≥0) :
    mutualInfoOfChannel (gaussianReal 0 P) (awgnChannel N h_meas) ≠ ⊤ := by
  by_cases hN : N = 0
  · -- 退化: N = 0、決定論 channel W x = dirac x、MI finite (= 0)。別 branch。
    subst hN
    sorry  -- @residual(plan:parallel-gaussian-l-pg1-discharge-plan) — N=0 deterministic branch
  · -- 主 branch: N ≠ 0。klDiv_ne_top に AC + llr integrability を渡す。
    set p := gaussianReal 0 P with hp
    set W := awgnChannel N h_meas with hW
    set q := outputDistribution p W with hq
    -- output Gaussian (IsAwgnOutputGaussian) を AWGNMIBridgeDischarge から取得
    -- → hWx_q : ∀ x, W x ≪ q ; hq_vol : q ≪ volume ; h_joint_ac : p ⊗ₘ W ≪ p.prod q
    rw [mutualInfoOfChannel_def, jointDistribution_def]
    refine klDiv_ne_top ?_ ?_
    · -- AC: ContChannelMIDecomp.lean:556-559 と同型
      sorry
    · -- llr integrability: split + (fibre − output) .sub
      sorry
```

埋め順: (1) 主 branch の AC（既存 inline コピー、最易）→ (2) 主 branch llr integrability
（split + `.sub`、analytic core 既存）→ (3) `N=0` 退化 branch（最後、決定論 klDiv）。

---

## 検証ノート（verbatim 確認済の数値・型）

- `gaussianReal μ 0 = Measure.dirac μ`（`Real.lean:207`、`@[simp] gaussianReal_zero_var`）。
- `mutualInfoOfChannel` の中身 = `klDiv (p ⊗ₘ W) (p.prod (p⊗ₘW).snd)`（`ChannelCoding.lean:85,55,72`）。
- `klDiv_ne_top` は measure に型クラス前提ゼロ（`Basic.lean:53,103`）。
- 既存 finite-alphabet 版 `mutualInfo_ne_top`（`MutualInfo.lean:197`）は `[Fintype X][Fintype Y]` +
  helper が `lintegral_fintype` / singleton 分解依存（`:189,151`）→ **連続 Y=ℝ では reuse 不可**を
  verbatim 確認。連続版は本 inventory の §B+C route で独立に構築する。
- 既存 `klDiv_ne_top` 呼出 3 site（`Stein.lean:949`, `Bridge.lean:447`, `MaxEntropy.lean:119`）は
  すべて Fintype 上で `lintegral_fintype` により llr integrability を供給（連続版に直接 reuse 不可、
  パターンのみ参照）。
```
