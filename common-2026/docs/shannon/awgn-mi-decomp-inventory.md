# AWGN MI 分解 bridge (`IsContChannelMIDecompHyp`) のための Mathlib 在庫 + 実現可能性判定

> 対象: `IsContChannelMIDecompHyp p W` (`Common2026/Shannon/AWGNMIDecompBody.lean:144`) の body 化。
> すなわち連続チャネルの MI chain rule `I(X;Y) = h(Y) − h(Y|X)`。
> 親計画の撤退ライン: `awgn-moonshot-plan.md` §撤退ライン **F-2** (`h_mi_bridge` hypothesis 外出し)。
> 既存同種文書: [`shannon-mathlib-inventory.md`](shannon-mathlib-inventory.md), [`awgn-mathlib-inventory.md`](awgn-mathlib-inventory.md)。

## 一行サマリ

**実現可能性 = CONDITIONAL-YES。** KL→積分展開 (`toReal_klDiv_of_measure_eq`)、compProd 連鎖律 (`integral_llr_compProd_eq_add`, `rnDeriv_compProd`)、Fubini (`Measure.integral_compProd`)、`prod = compProd const` (`Measure.compProd_const`) はすべて Mathlib 既存。**density-level の核心インフラは 100% ある。** 自作が必要なのは「KL の log-likelihood-ratio 積分 (`∫∫ log (dW_x/dq)`) を 2 本の differential-entropy 積分 (`-h(Y|X) + h(Y)`) に組み替える bridge」**1 本のみ** — rnDeriv の三角律 (`rnDeriv_mul_rnDeriv`) で `dW_x/dq = (dW_x/dvol)/(dq/dvol)` に砕き、log を分解する **density 同定補題** が project にも Mathlib にも無い。これが唯一の真の自作項目で、**推定 150–220 行**(整合性・integrability 込み)。`≪volume` + 4 本の integrability を honest 仮定として残せば本体は閉じる。**撤退ライン F-2 発動 = NO**(F-2 を縮退させ body 化に踏み込める)、ただし F-2′ として「density 同定補題 + integrability」を named hyp に残す縮退案を提案。

---

## 主定理の最終形 (再掲)

`Common2026/Shannon/AWGNMIDecompBody.lean:144-149` verbatim:

```lean
def IsContChannelMIDecompHyp
    (p : Measure ℝ) (W : InformationTheory.Shannon.ChannelCoding.Channel ℝ ℝ) : Prop :=
  (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel p W).toReal
    = Common2026.Shannon.differentialEntropy
        (InformationTheory.Shannon.ChannelCoding.outputDistribution p W)
      - (∫ x, Common2026.Shannon.differentialEntropy (W x) ∂p)
```

project 側の関連定義 (verbatim, file:line):

- `mutualInfoOfChannel p W := klDiv (jointDistribution p W) (p.prod (outputDistribution p W))` — `ChannelCoding.lean:84`
- `jointDistribution p W := p ⊗ₘ W` — `ChannelCoding.lean:54`
- `outputDistribution p W := (jointDistribution p W).snd` — `ChannelCoding.lean:71`
- `Channel α β := Kernel α β` (`abbrev`) — `ChannelCoding.lean:49`
- `differentialEntropy μ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume` — `DifferentialEntropy.lean:42` (= `-∫ f log f`, `f = dμ/dvol`)

証明戦略 (pseudo-Lean、適用予定の Mathlib 補題を併記):

```lean
-- 前提: [IsProbabilityMeasure p], [IsMarkovKernel W], q := outputDistribution p W,
--       p⊗ₘW ≪ p.prod q (= p ⊗ₘ const q),  W x ≪ vol (∀x), q ≪ vol,
--       4 本の integrability (下記 §可積分性)
mutualInfoOfChannel p W                                    -- = klDiv (p⊗ₘW) (p.prod q)
  |>.toReal
  = ∫ z, llr (p⊗ₘW) (p.prod q) z ∂(p⊗ₘW)                  -- toReal_klDiv_of_measure_eq (両者 prob, univ=1)
  = ∫ x, ∫ y, log ((p⊗ₘW).rnDeriv (p.prod q) (x,y)).toReal ∂(W x) ∂p   -- Measure.integral_compProd (Fubini) + llr_def
  = ∫ x, ∫ y, log ((W x).rnDeriv vol y / q.rnDeriv vol y).toReal ∂(W x) ∂p
                                                            -- ★自作 density 同定: rnDeriv_compProd + rnDeriv_mul_rnDeriv で
                                                            --   (p⊗ₘW)/(p⊗ₘ const q) (x,y) = (dW_x/dvol)(y) / (dq/dvol)(y)
  = ∫ x, ∫ y, [log f_{W x}(y) − log f_q(y)] · f_{W x}(y) dy ∂p          -- log_div + W x = vol.withDensity f_{Wx}
  = − (∫ x, differentialEntropy (W x) ∂p) + differentialEntropy q       -- negMulLog 定義 + cross-entropy 同定
```

---

## API 在庫テーブル

### A. KL → 積分展開 (`InformationTheory/KullbackLeibler/Basic.lean`)

| 概念 | Mathlib API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| `klDiv` 定義 | `noncomputable irreducible_def klDiv (μ ν : Measure α) : ℝ≥0∞ := if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ − μ.real univ) else ∞` | `Basic.lean:57` | 🟢 | `mutualInfoOfChannel` の本体。`irreducible_def` ⇒ 展開は `klDiv_def`/専用補題経由 |
| **KL の toReal = ∫ llr (univ 等しい版)** | `toReal_klDiv_of_measure_eq (h : μ ≪ ν) (h_eq : μ univ = ν univ) : (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ` | `Basic.lean:164` | 🟢 **主役** | step 1: integrability 仮定不要。`p⊗ₘW` も `p.prod q` も prob ⇒ `univ = 1` 一致で前提充足 |
| KL toReal (一般) | `toReal_klDiv (h : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ + ν.real univ − μ.real univ` | `Basic.lean:157` | 🟢 | univ 不一致時の fallback (本件不要) |
| `llr` 定義 | `noncomputable def llr (μ ν : Measure α) (x : α) : ℝ := log (μ.rnDeriv ν x).toReal` | `MeasureTheory/Measure/LogLikelihoodRatio.lean:37` | 🟢 | `llr = log rnDeriv`。step 3 で density 砕きの足場 |
| `llr_def` | `llr μ ν = fun x ↦ log (μ.rnDeriv ν x).toReal` | 同 `:39` | 🟢 | 同上 (rfl) |

型クラス前提 (Basic.lean section): `{α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}`。`toReal_klDiv_of_measure_eq` 自体は追加インスタンス不要。

### B. compProd 連鎖律 — rnDeriv 分解 (`Probability/Kernel/Composition/RadonNikodym.lean`)

| 概念 | Mathlib API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| **compProd rnDeriv 連鎖律 (full)** | `rnDeriv_compProd [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) (ν : Measure α) [IsFiniteMeasure ν] : (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] (fun p ↦ μ.rnDeriv ν p.1 * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p)` | `RadonNikodym.lean:107` | 🟢 **核心** | step 3 の出発点。本件 `μ=ν=p` ⇒ 第1因子 `p.rnDeriv p = 1` |
| **compProd rnDeriv (同 kernel)** | `rnDeriv_measure_compProd_left (μ ν : Measure α) (κ : Kernel α β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] : (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ) =ᵐ[ν ⊗ₘ κ] fun p ↦ (μ.rnDeriv ν) p.1` | `RadonNikodym.lean:92` | 🟢 | `klDiv_compProd_left` 経由で間接利用 |
| compProd rnDeriv (withDensity 補助) | `rnDeriv_compProd_withDensity_rnDeriv (μ ν : Measure α) (κ η : Kernel α β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] : (ν.withDensity (μ.rnDeriv ν) ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)` | `RadonNikodym.lean:77` | 🟢 | 上の内部補題。直接は使わない見込み |

⚠️ **前提**: `rnDeriv_compProd` は **`[IsFiniteKernel κ] [IsFiniteKernel η]` 要求**。`Channel = Kernel`、AWGN の `awgnChannel` は `IsMarkovKernel` (`AWGN.lean:82`) ⇒ `IsFiniteKernel` 自動。`Kernel.const _ q` も `q` が prob ⇒ `IsMarkovKernel`。**満たせる**。ただし抽象 `IsContChannelMIDecompHyp p W` で `W` に `[IsMarkovKernel W]` 前提が現状の def signature に**無い** — body 化時に **`W` 側へ `[IsMarkovKernel W]` (または `IsFiniteKernel`) を足す必要**(下記 §自作 落とし穴 1)。

### C. rnDeriv 三角律 — density 砕き (`MeasureTheory/Measure/Decomposition/RadonNikodym.lean`)

| 概念 | Mathlib API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| **rnDeriv 推移律 (`κ`-ae)** | `Measure.rnDeriv_mul_rnDeriv {μ ν κ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ] (hμν : μ ≪ ν) : μ.rnDeriv ν * ν.rnDeriv κ =ᵐ[κ] μ.rnDeriv κ` | `RadonNikodym.lean:402` | 🟢 **核心** | `(dW_x/dq) · (dq/dvol) = dW_x/dvol` ⇒ `dW_x/dq = (dW_x/dvol)/(dq/dvol)` の砕きに使う |
| rnDeriv 推移律 (`ν`-ae) | `Measure.rnDeriv_mul_rnDeriv' (hνκ : ν ≪ κ) : μ.rnDeriv ν * ν.rnDeriv κ =ᵐ[ν] μ.rnDeriv κ` | `RadonNikodym.lean:410` | 🟢 | ae-基底が `ν` 側のとき用の variant |
| rnDeriv ↔ withDensity | `Measure.rnDeriv_withDensity (μ : Measure α) {f} (hf : Measurable f) : (μ.withDensity f).rnDeriv μ =ᵐ[μ] f` | (`DifferentialEntropy.lean:53` で既使用) | 🟢 | `W x = vol.withDensity f_{Wx}` ⇒ `(W x).rnDeriv vol =ᵐ f_{Wx}`。fibre density 同定 |

### D. Fubini / 積分 compProd (`Probability/Kernel/Composition/IntegralCompProd.lean`)

| 概念 | Mathlib API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| **measure-level Fubini** | `MeasureTheory.integral_compProd [SFinite μ] [IsSFiniteKernel κ] {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α × β → E} (hf : Integrable f (μ ⊗ₘ κ)) : ∫ x, f x ∂(μ ⊗ₘ κ) = ∫ a, ∫ b, f (a, b) ∂(κ a) ∂μ` | `IntegralCompProd.lean:473` | 🟢 **主役** | step 2: `∫ ... ∂(p⊗ₘW) = ∫∫ ... ∂(W x) ∂p`。**`Integrable f (p⊗ₘW)` を要求** ⇒ honest 仮定 1 本 |
| kernel-level Fubini | `ProbabilityTheory.integral_compProd (hf : Integrable f ((κ⊗ₖη) a)) : ∫ z, f z ∂(κ⊗ₖη) a = ∫ x, ∫ y, f (x,y) ∂η (a,x) ∂κ a` | 同 `:237` | 🟢 | measure 版の土台 |
| compProd integrable 判定 | `Measure.integrable_compProd_iff (hf : AEStronglyMeasurable f (μ⊗ₘκ)) : Integrable f (μ⊗ₘκ) ↔ (∀ᵐ x ∂μ, Integrable (fun y => f (x,y)) (κ x)) ∧ Integrable (fun x => ∫ y, ‖f (x,y)‖ ∂(κ x)) μ` | 同 `:466` | 🟢 | honest integrability を fibrewise に砕く |

### E. `prod = compProd const` 翻訳 (`Probability/Kernel/Composition/MeasureCompProd.lean`)

| 概念 | Mathlib API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| **`Measure.prod = compProd (const)`** | `MeasureTheory.Measure.compProd_const {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] : μ ⊗ₘ (Kernel.const α ν) = μ.prod ν` | `MeasureCompProd.lean:141` | 🟢 **主役** | `mutualInfoOfChannel` の右側 `p.prod q` を `p ⊗ₘ const q` に書換 ⇒ §B/C の compProd 機械を発動 |
| `Kernel.const` 定義 | `ProbabilityTheory.Kernel.const (α) {β} (μβ : Measure β) : Kernel α β` | `Kernel/Basic.lean:178` (shannon-inventory §F) | 🟢 | `η := const _ q`、`q` prob ⇒ Markov |
| `klDiv_compProd_left` | `klDiv_compProd_left (μ ν : Measure 𝓧) (κ : Kernel 𝓧 𝓨) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν` (`@[simp]`) | `ChainRule.lean:182` | 🟢 | (代替経路) `klDiv p p = 0` 同定の補助 |
| `klDiv_compProd_eq_add` | `klDiv_compProd_eq_add (μ ν : Measure 𝓧) (κ η : Kernel 𝓧 𝓨) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η] : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` | `ChainRule.lean:204` | 🟡 補助 | chain rule。本件は `μ=ν=p` で第1項 `klDiv p p = 0` ⇒ `MI = klDiv (p⊗ₘW)(p⊗ₘ const q)`。**ただし MI 公式の本質は §F の積分形** |

### F. log-likelihood-ratio 積分の連鎖律 — entropy 分解の直前まで (`ChainRule.lean`)

| 概念 | Mathlib API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| **llr 積分の chain rule** | `integral_llr_compProd_eq_add (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η) (h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)) : ∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂μ⊗ₘκ = ∫ a, llr μ ν a ∂μ + ∫ p, llr (μ ⊗ₘ κ) (μ ⊗ₘ η) p ∂(μ ⊗ₘ κ)` | `ChainRule.lean:151` | 🟢 (任意) | `μ=ν=p`: 第1項 `∫ llr p p ∂p = 0` ⇒ `MI.toReal = ∫ llr (p⊗ₘW)(p⊗ₘconst q) ∂(p⊗ₘW)`。**§A→§D 経路で代替可なので必須ではない** |
| llr 積分連鎖の integrability 判定 | `integrable_llr_compProd_iff (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η) : Integrable (llr (μ⊗ₘκ)(ν⊗ₘη)) (μ⊗ₘκ) ↔ Integrable (llr μ ν) μ ∧ Integrable (llr (μ⊗ₘκ)(μ⊗ₘη)) (μ⊗ₘκ)` | `ChainRule.lean:115` | 🟡 | honest integrability を分解する道具 |
| rnDeriv log 積形 (ae) | `rnDeriv_compProd_mul_log_eq_mul_add (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) : ∀ᵐ p ∂(ν⊗ₘη), ((∂μ⊗ₘκ/∂ν⊗ₘη) p).toReal * log (...) = (...).toReal * (log ((∂μ/∂ν) p.1).toReal + log ((∂(μ⊗ₘκ)/∂(μ⊗ₘη)) p).toReal)` | `ChainRule.lean:103` | 🟡 | density log 砕きの ready-made (ただし `dvol` への落とし込みは別)|

ChainRule.lean section 型クラス (`:88-90` verbatim):
`{𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {μ ν : Measure 𝓧} {κ η : Kernel 𝓧 𝓨} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η]`。
→ `klDiv_compProd_*` / `integral_llr_compProd_*` は **両 kernel に `IsMarkovKernel` を要求**。

### G. differential-entropy 側 (project 自作、`Common2026/Shannon/DifferentialEntropy.lean`)

| 概念 | Mathlib/project API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| `differentialEntropy` 定義 | `differentialEntropy μ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume` | `DifferentialEntropy.lean:42` | 🟢 既存 | 主定理両辺の単位 |
| **density 形 entropy** | `differentialEntropy_eq_integral_density {f : ℝ→ℝ} (hf : Measurable f) (hf_nn : ∀ x, 0 ≤ f x) (μ) (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) : differentialEntropy μ = -∫ x, f x * Real.log (f x) ∂volume` | `DifferentialEntropy.lean:60` | 🟢 **主役** | `h(W x) = -∫ f_{Wx} log f_{Wx}`、`h(q) = -∫ f_q log f_q`。step 5 の終端形 |
| withDensity 形 entropy | `differentialEntropy_eq_integral_withDensity {f : ℝ→ℝ≥0∞} (hf : Measurable f) : differentialEntropy (volume.withDensity f) = ∫ x, Real.negMulLog (f x).toReal ∂volume` | `DifferentialEntropy.lean:47` | 🟢 | density が `ℝ≥0∞` 形のとき |
| `Real.negMulLog` 定義 | `noncomputable def Real.negMulLog (x : ℝ) : ℝ := - x * log x` | `Analysis/SpecialFunctions/Log/NegMulLog.lean:164` | 🟢 | `negMulLog f = -(f log f)` |

---

## 主要前提条件ボックス (前提事故が起きやすい lemma)

- **`toReal_klDiv_of_measure_eq` (`Basic.lean:164`)**: 前提は `μ ≪ ν` と `μ univ = ν univ` の **2 本のみ**。integrability 不要なのが利点。本件: `μ = p⊗ₘW`, `ν = p.prod q`、両者 prob measure ⇒ `univ = 1` 一致は `measure_univ` で即。`p⊗ₘW ≪ p.prod q` は **honest 仮定** (= `≪ vol` 群から導けるが要 plumbing)。
- **`rnDeriv_compProd` (`RadonNikodym.lean:107`)**: `[IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure ν]` + `h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η`。**ae 等式 (`=ᵐ[ν ⊗ₘ η]`)** で返る ⇒ 後続の `integral_congr_ae` で食わせる。`ν` は free、本件 `ν := p`。
- **`Measure.integral_compProd` (Fubini, `IntegralCompProd.lean:473`)**: `[SFinite μ] [IsSFiniteKernel κ]` + **`Integrable f (μ ⊗ₘ κ)`**。被積分 `f = llr (p⊗ₘW)(p.prod q)` の `p⊗ₘW`-可積分性が honest 仮定の最大の置き場。`integrable_compProd_iff` で fibrewise 化可。
- **`Measure.rnDeriv_mul_rnDeriv` (`RadonNikodym.lean:402`)**: `[SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ]` + `μ ≪ ν`。**ae 等式は `κ`-基底** (`=ᵐ[κ]`)。本件で `κ := vol`、`μ := W x`、`ν := q` ⇒ `(dW_x/dq)·(dq/dvol) = dW_x/dvol` を `vol`-ae で得る。`W x ≪ q` が要 ⇒ honest 仮定 (各 fibre が output に吸収される、`≪ vol` から)。
- **`differentialEntropy_eq_integral_density` (`DifferentialEntropy.lean:60`)**: `f` measurable + `0 ≤ f` + `μ = vol.withDensity (ofReal ∘ f)`。各 fibre `W x` と output `q` を density `f_{Wx}`, `f_q` で表す **density 表現が honest 仮定** (`≪ vol` ⇒ `Measure.withDensity_rnDeriv_eq` で取れるが、整合に plumbing)。

---

## 自作が必要な要素 (優先度順)

### 1. ★ **density 同定 bridge** — 唯一の真の自作項目 (推定 150–220 行)

llr 積分 `∫∫ log ((p⊗ₘW).rnDeriv (p.prod q) (x,y)).toReal` を 2 本の density 積分

```
− ∫ x (∫ y, f_{Wx}(y) log f_{Wx}(y) dy) ∂p   +   ∫ y, f_q(y) log f_q(y) dy
```

に組み替える補題。Mathlib にも project にも無い。**推奨実装**:

1. `Measure.compProd_const` で `p.prod q = p ⊗ₘ const q`。
2. `rnDeriv_compProd` (μ=ν=p) で `(p⊗ₘW).rnDeriv (p⊗ₘ const q) (x,y) =ᵐ (p.rnDeriv p x)·((p⊗ₘW).rnDeriv (p⊗ₘ const q) (x,y))` の第1因子を `rnDeriv_self = 1` で潰し、`(W x).rnDeriv q y` の形に落とす(`rnDeriv_measure_compProd_left`/`const` 経由で fibre rnDeriv を取り出す)。
3. `rnDeriv_mul_rnDeriv` で `(W x).rnDeriv q y = (W x).rnDeriv vol y / q.rnDeriv vol y` (vol-ae, `W x ≪ q ≪ vol`)。
4. `log_div` + `Measure.integral_compProd` (Fubini) で `∫∫ [log f_{Wx} − log f_q] dW_x dp`。
5. 内側を `W x = vol.withDensity f_{Wx}` で `∫ y, f_{Wx} log f_{Wx} dvol` に変換 (`lintegral`/`integral` の withDensity 公式)、`differentialEntropy_eq_integral_density` で `-h(W x)`。
6. `q` 項は `x` に依らない ⇒ `∫ x ... ∂p = (∫ x dW_x... の y-marginal) = ∫ y f_q log f_q dvol` を **output marginal = `p ⊗ₘ W` の y-周辺 = q** で同定 (`Measure.snd` / Fubini)。これが `h(q)`。

**落とし穴**:
- (落とし穴 1) `IsContChannelMIDecompHyp` の現 def signature に **`[IsMarkovKernel W]` が無い**。body 化補題は `W` に `[IsMarkovKernel W]` (or `IsFiniteKernel` + Markov for `compProd_const`/`integral_compProd`) を**追加引数として持つ別 lemma**で書き、`awgn_midecomp_of_cont_chain` (`:160`) は AWGN の Markov instance を渡して接続する形になる。def 自体は触らず済む見込みだが、抽象 body lemma の signature は太る。
- (落とし穴 2) step 6 の output-density 同定 `f_q(y) = ∫ x, p(dx)·f_{Wx}(y)` (mixture density) を陽に通すなら追加 plumbing。**output `q` を直接 `vol.withDensity f_q` と仮定**(honest)すれば回避でき、AWGN では `q = gaussianReal 0 (P+N)` で具体的に取れる(`awgn_output_absolutelyContinuous_of_outputGaussian`, `:111`)。
- (落とし穴 3) `negMulLog 0 = 0` の境界処理。`f_{Wx}(y) = 0` の点で `log` が暴れるが `negMulLog`/`klFun` が 0 で連続拡張済み ⇒ `rnDeriv = 0` 分岐を `simp` で吸収。

### 2. integrability 補助補題 (推定 30–50 行、または honest 仮定で外出し)

`Integrable (llr (p⊗ₘW)(p.prod q)) (p⊗ₘW)` と `Integrable (f_{Wx} log f_{Wx}) vol` (∀ x ae) と `Integrable (f_q log f_q) vol`。AWGN では `integrable_density_log_density_of_gaussian` (`DifferentialEntropy.lean:81`) が fibre/output の Gaussian 版を**既に与える** ⇒ AWGN instance では discharge 可。抽象版は **honest 仮定として残すのが安全**。

---

## 必要になる honest 仮定の正確なリスト

body lemma に渡す named hypothesis (AWGN instance では §G/Phase A で全て discharge 可、抽象版では残す):

1. `hW_ac : ∀ x, W x ≪ volume` — 各 fibre が density を持つ。AWGN: `awgnChannel_apply_absolutelyContinuous` (`:101`) で済。
2. `hq_ac : outputDistribution p W ≪ volume` — output が density を持つ。AWGN: `awgn_output_absolutelyContinuous_of_outputGaussian` (`:111`)。
3. `h_joint_ac : (p ⊗ₘ W) ≪ p.prod (outputDistribution p W)` — KL 展開と rnDeriv 連鎖の前提。1+2 + `absolutelyContinuous_compProd_iff` から導出可だが plumbing。
4. `h_int_llr : Integrable (llr (p⊗ₘW) (p.prod q)) (p⊗ₘW)` — Fubini 前提。
5. `h_int_fibre : ∀ᵐ x ∂p, Integrable (fun y => f_{Wx} y * log (f_{Wx} y)) volume` — fibre entropy 有限。AWGN: Gaussian 版既存。
6. `h_int_out : Integrable (fun y => f_q y * log (f_q y)) volume` — output entropy 有限。AWGN: Gaussian 版既存。
7. (任意) `hW_markov : IsMarkovKernel W` (or `IsFiniteKernel`) — §B/D/E の型クラス前提。

→ **抽象 `IsContChannelMIDecompHyp` を body 化するなら 1–7 を引数に持つ補題を立て、現 def → その補題 + AWGN discharge で接続**。これが撤退ライン F-2 の縮退 (F-2′)。

---

## 撤退ラインへの距離

親計画 `awgn-moonshot-plan.md` §撤退ライン **F-2**: MI bridge を `h_mi_bridge` hypothesis として converse 全体へ外出し。現状 `AWGNMIDecompBody.lean` は F-2 を **`IsContChannelMIDecompHyp` (AWGN 非依存版) へ縮減**して named hyp に残す形 (Phase B deferred)。

**判定: 撤退ライン F-2 発動 = NO (踏み抜かない)。**

- 核心インフラ (§A〜§G) は **density-level で 100% 既存**。compProd rnDeriv 連鎖律 (`rnDeriv_compProd`)・llr 積分連鎖 (`integral_llr_compProd_eq_add`)・Fubini・`prod=compProd const`・`differentialEntropy_eq_integral_density` がすべて揃う。
- 自作は **density 同定 bridge 1 本 (§自作 1) + integrability (§自作 2)**。後者は AWGN instance では `integrable_density_log_density_of_gaussian` で discharge 済み。
- ⇒ `IsContChannelMIDecompHyp` を **body 化できる見込み**。F-2 を「named hyp 据え置き」で温存する必要は無い。

**新規縮退案 F-2′ (本 inventory 提案)**: もし §自作 1 step 6 の output-density mixture 同定が想定超え (mixture density の Fubini が重い) の場合 → **「density 同定 bridge」を `output q = vol.withDensity f_q` (honest) + 上記仮定 1–6 を引数に取る named lemma で立て**、AWGN では §G/Phase A + Gaussian で全て discharge。これは F-2 の「MI 公式まるごと hypothesis」より**1 段階具体的**(MI 公式の density 構造を陽に固定し、残すのは density 表現 + integrability のみ)。2 週間で §自作 1 が閉じなければ F-2′ へ縮退。

---

## 着手 skeleton

`Common2026/Shannon/ContChannelMIDecomp.lean` の出だし (新規ファイル想定):

```lean
import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.DifferentialEntropy
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

variable {p : Measure ℝ} [IsProbabilityMeasure p]
variable {W : Channel ℝ ℝ} [IsMarkovKernel W]

/-- ★自作 1: KL の llr 積分 = `−h(Y|X) + h(Y)`。density 同定 bridge。 -/
theorem mutualInfoOfChannel_toReal_eq_diffEntropy_sub
    (hW_ac : ∀ x, W x ≪ volume)
    (hq_ac : outputDistribution p W ≪ volume)
    (h_joint_ac : (p ⊗ₘ W) ≪ p.prod (outputDistribution p W))
    (h_int_llr : Integrable (llr (p ⊗ₘ W) (p.prod (outputDistribution p W))) (p ⊗ₘ W))
    -- fibre / output integrability (honest)
    (h_int_fibre : True)   -- placeholder: ∀ᵐ x ∂p, Integrable (f_{Wx} log f_{Wx}) volume
    (h_int_out  : True) :  -- placeholder: Integrable (f_q log f_q) volume
    (mutualInfoOfChannel p W).toReal
      = Common2026.Shannon.differentialEntropy (outputDistribution p W)
        - (∫ x, Common2026.Shannon.differentialEntropy (W x) ∂p) := by
  sorry  -- §証明戦略 step 1-6: toReal_klDiv_of_measure_eq → integral_compProd
         --   → rnDeriv_compProd + rnDeriv_mul_rnDeriv → log_div
         --   → differentialEntropy_eq_integral_density

end InformationTheory.Shannon.ChannelCoding
```

`AWGNMIDecompBody.lean` の `awgn_midecomp_of_cont_chain` (`:160`) は、本補題に AWGN の `IsMarkovKernel`/`≪ vol`/Gaussian integrability を渡して `IsContChannelMIDecompHyp` を discharge する形へ差し替え。
