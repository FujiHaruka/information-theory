# AWGN single-letter capacity converse (max-entropy 壁) — Mathlib API 在庫調査

> 対象 wall: `@residual(wall:awgn-capacity-converse-maxent)`
> (`docs/audit/audit-tags.md` Wall name register、`InformationTheory/Draft/Shannon/ContChannelMIDecomp.lean:670` `awgn_capacity_closed_form_of_out` body 内 `h_max_ent` の `sorry`)
> 親計画: `docs/shannon/awgn-moonshot-plan.md` (撤退ライン F-3) / 隣接 `docs/shannon/awgn-converse-c1b-gaussian-maxent-mini-plan.md`
> 同種文書: `docs/shannon/awgn-mi-decomp-inventory.md` / `docs/shannon/awgn-converse-aux-mathlib-inventory.md`

---

## 暫定結論 (在庫からの判断、3–5 行)

**(ii) プロジェクト内自作 real-analysis 補題が 5〜6 本必要** に該当する。「真に重い無限の壁」ではない。MI→entropy 差分解 (`mutualInfoOfChannel_toReal_eq_diffEntropy_sub`, **0 sorry 完成済**) と Gaussian max-entropy (`differentialEntropy_le_gaussian_of_variance_le`, **既存**) という 2 つの主役は in-tree で揃い、分散・畳み込み・PDF・可積分性の素材も Mathlib にほぼ全て存在する。**唯一の真の Mathlib 不在**は「mixture-of-Gaussians 出力密度 `p ∗ 𝒩(0,N)` の `log`/`negMulLog` 可積分性」(loogle `Found 0`) だが、これは原理的に self-derivable: `rnDeriv_conv` (Mathlib にある畳み込み rnDeriv = pdf の Lebesgue 畳み込み) + Gaussian pdf の上下界 + 二次モーメント有限性から組める。最大の落とし穴は **`differentialEntropy_le_gaussian_of_variance_le` の `h_var : ∫(x−m)² ≤ v` が「平均 m での分散」を要求する点** — converse では `Var(Y) ≤ E[Y²] ≤ E[X²]+N` を使うため、`m = E[Y]` を取った上で `Var(Y) ≤ E[X²]+N` を `IndepFun.variance_add` から導く plumbing が要る。

---

## 主定理の最終形 (再掲)

`InformationTheory/Draft/Shannon/ContChannelMIDecomp.lean:670-702` `awgn_capacity_closed_form_of_out`、その body 内の唯一の `sorry` (L692) が本壁:

```lean
-- h_max_ent (closed form converse の核): ∀ 確率測度 p with ∫x²∂p ≤ P,
theorem (target form):
    ∀ p ∈ { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P },
      (mutualInfoOfChannel p (awgnChannel N (isAwgnChannelMeasurable N))).toReal
        ≤ (1/2) * Real.log (1 + P / (N : ℝ))
```

証明戦略 (Cover-Thomas 9.1 converse、pseudo-Lean):

```lean
intro p ⟨hp_prob, hp_2mom⟩
set q := outputDistribution p (awgnChannel N _)   -- q = p ∗ 𝒩(0,N) (continuous mixture)
-- 1. MI = h(Y) − h(Y|X)  [既存 chain rule、要 4+ regularity/integrability hyp]
have h_mi : (mutualInfoOfChannel p W).toReal
          = differentialEntropy q − ∫ x, differentialEntropy (W x) ∂p
        := mutualInfoOfChannel_toReal_eq_diffEntropy_sub  hW_ac hWx_q hq_ac h_joint_ac
             (g := gaussianPDF) measurable_gaussianPDF_uncurry hg_ae
             h_int_fibre h_int_out            -- ★ h_int_out が本壁 (output log-density 可積分)
-- 2. h(Y|X) = ∫ h(𝒩(x,N)) dp = (1/2)log(2πeN)  [Gaussian fibre entropy 定数]
have h_cond : ∫ x, differentialEntropy (W x) ∂p = (1/2)*log(2πeN)
        := by simp [awgnChannel_apply, differentialEntropy_gaussianReal]
-- 3. h(Y) ≤ (1/2)log(2πe·Var(Y))  [Gaussian max-entropy、既存だが 4 hyp]
have h_maxent : differentialEntropy q ≤ (1/2)*log(2πe*(Var Y))
        := differentialEntropy_le_gaussian_of_variance_le hq_ac (m := E[Y]) hv h_mean h_var
             h_var_int h_ent_int               -- ★ h_ent_int も本壁 (= h_int_out 同型)
-- 4. Var(Y) ≤ E[X²] + N ≤ P + N  [IndepFun.variance_add + variance_le_expectation_sq]
have h_var_le : Var(Y) ≤ P + N := ...
-- 5. 算術: (1/2)log(2πe(P+N)) − (1/2)log(2πeN) = (1/2)log(1+P/N)
linarith [...] -- log algebra (既存 mutualInfoOfChannel_gaussianInput_closed_form と同型)
```

---

## API 在庫テーブル

> 全 signature は verbatim。`[...]` 型クラス前提は括弧を落とさず転記。Mathlib 不在は loogle 結果を併記。

### A. Gaussian 畳み込み密度の正則性 (mixture-of-Gaussians 出力 `p ∗ 𝒩(0,N)`)

| 概念 | Mathlib API | file:line | 状態 | 本壁での扱い |
|---|---|---|---|---|
| 測度畳み込み (加法形) | `MeasureTheory.Measure.conv` | `Mathlib/MeasureTheory/Group/Convolution.lean:35` (`@[to_additive]` of `mconv`) | ✅ 既存 | 出力 `q` を `p ∗ 𝒩(0,N)` で表す本体 |
| Giry-bind = 畳み込み | `bind_eq_conv_of_translation_kernel` (in-tree) | `InformationTheory/Shannon/AWGNBindConvBody.lean:78` | ✅ 既存 (genuine) | `κ ∘ₘ p = p ∗ ν`、**任意 SFinite `p`** で成立 (Gaussian 入力に限らない) |
| compProd の snd = composition | `MeasureTheory.Measure.snd_compProd` | `Mathlib/Probability/Kernel/Composition/MeasureComp.lean` | ✅ 既存 | `outputDistribution p W = (p⊗ₘW).snd = W ∘ₘ p` を `p ∗ 𝒩(0,N)` に橋渡し |
| **畳み込みの rnDeriv = pdf の Lebesgue 畳み込み** | `MeasureTheory.rnDeriv_conv` (加法形) | `Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean:653` (`@[to_additive]` of `rnDeriv_mconv`) | ✅ **既存 (最重要)** | mixture 出力密度の構造を与える。下記 signature 注意 |
| 畳み込み = withDensity(lconv rnDeriv) | `MeasureTheory.conv_eq_withDensity_lconvolution_rnDeriv` | `RadonNikodym.lean:638` (`@[to_additive]` of `mconv_eq_withDensity_mlconvolution_rnDeriv`) | ✅ 既存 | 同上、withDensity 形 |
| 独立和の pdf = pdf の Lebesgue 畳み込み | `ProbabilityTheory.IndepFun.pdf_add_eq_lconvolution_pdf` | `Mathlib/Probability/Density.lean:357` (`@[to_additive]` of `_mul_`) | ✅ 既存 | `pdf` API 経由のもう一つの密度表示 |
| Lebesgue 畳み込み定義 (積分形) | `MeasureTheory.lconvolution` / `lconvolution_def` | `Mathlib/Analysis/LConvolution.lean:50` / `:68` (`@[to_additive]`) | ✅ 既存 | `(f ⋆ₗ[μ] g) x = ∫⁻ y, f y * g(−y+x) ∂μ` の明示形 |
| 畳み込みの可測性 | `MeasureTheory.measurable_lconvolution` | `Mathlib/Analysis/LConvolution.lean:90` (`@[to_additive]` of `measurable_mlconvolution`) | ✅ 既存 | 出力密度の可測性 |
| 畳み込みの絶対連続性 | `MeasureTheory.Measure.conv_absolutelyContinuous` | `Convolution.lean:166` 付近 (`@[to_additive]` of `mconv_absolutelyContinuous`) | ✅ 既存 | `q ≪ volume` (`hq_ac`) を供給 |
| Gaussian ∗ Gaussian = Gaussian | `ProbabilityTheory.gaussianReal_conv_gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:613` | ✅ 既存 | Gaussian 入力時のみ (一般 `p` には不適用、参考) |
| **Gaussian pdf の上界 `≤ 1/√(2πv)`** | — | — | ❌ **不在** (loogle `gaussianPDFReal, (_ ≤ _)` → `_nonneg` / `_mul` のみ) | 自作 (簡単: exp 因子 ≤ 1)。出力密度の上界 → log の上界に使う |
| Gaussian pdf 正値 / 非負 | `ProbabilityTheory.gaussianPDFReal_pos` / `_nonneg` | `Gaussian/Real.lean` | ✅ 既存 | 下界 (log が −∞ にならない) |

**`rnDeriv_conv` の正確な signature** (`rnDeriv_mconv` の `@[to_additive]` twin、`RadonNikodym.lean:653` を verbatim):

```lean
@[to_additive]
theorem rnDeriv_mconv [SFinite μ] {ν₁ ν₂ : Measure G} [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    [ν₁.HaveLebesgueDecomposition μ] [ν₂.HaveLebesgueDecomposition μ]
    (hν₁ : ν₁ ≪ μ) (hν₂ : ν₂ ≪ μ) :
    (ν₁ ∗ₘ ν₂).rnDeriv μ =ᵐ[μ] (ν₁.rnDeriv μ) ⋆ₘₗ[μ] (ν₂.rnDeriv μ)
```

- section context (`RadonNikodym.lean:634-635`): `variable {G : Type*} [Group G] {mG : MeasurableSpace G} [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure G} [IsMulLeftInvariant μ]`。加法形では `[AddGroup G] [MeasurableAdd₂ G] [MeasurableNeg G] [IsAddLeftInvariant μ]`。
- ℝ + Lebesgue `volume` はこれらを全て満たす (`volume` は加法平行移動不変)。
- **結論は `=ᵐ[μ]`** (a.e. 等式)。density 値の everywhere の式ではない点に注意。
- **`HaveLebesgueDecomposition` + `IsFiniteMeasure` 前提**: `p` が確率測度なら自動。

### B. log・negMulLog の可積分性 (本壁の核心ピース)

| 概念 | Mathlib API | file:line | 状態 | 本壁での扱い |
|---|---|---|---|---|
| **`Integrable (log ((p∗𝒩).rnDeriv vol)) (p⊗ₘW)`** (`h_int_out`) | — | — | ❌ **不在 (真の壁、ただし self-derivable)** | 下記「自作」#3 |
| **`Integrable (negMulLog (q.rnDeriv vol)) volume`** (`h_ent_int`) | — | — | ❌ **不在 (同上、`h_int_out` と同型)** | 下記「自作」#3 |
| `Integrable (log ∘ f) μ` を陽に与える補題 | — | — | ❌ **不在** (loogle `Integrable (fun _ => Real.log _) _` → 0 match; `Integrable (fun _ => Real.negMulLog _) _` → 0) | 下記ブリッジ補題から組む |
| 可積分性の優関数比較 | `MeasureTheory.Integrable.mono` | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean` | ✅ 既存 | `|log f| ≤ (二次式)` で押さえる |
| 可積分性の優関数比較 (norm 形) | `MeasureTheory.Integrable.mono'` | `L1Space/Integrable.lean` | ✅ 既存 | 同上 |
| 有界 × 可積分 = 可積分 | `MeasureTheory.Integrable.bdd_mul` / `.bdd_mul'` | `L1Space/Integrable.lean` | ✅ 既存 | 補助 |
| Gaussian log-pdf は Gaussian 法則で可積分 (in-tree) | `integrable_log_gaussianPDFReal_gaussianReal` | `InformationTheory/Draft/Shannon/ContChannelMIDecomp.lean:404` | ✅ 既存 (genuine) | **fibre 側 `h_int_fibre` を供給** (AWGN fibre `W x = 𝒩(x,N)`)。output 側 `h_int_out` には直接使えない (mixture) |
| 二次差分 `(y−m)²` は Gaussian 法則で可積分 (in-tree) | `integrable_sq_sub_gaussianReal` | `ContChannelMIDecomp.lean:387` | ✅ 既存 (genuine) | `h_var_int` 系・log の二次優関数の素材 |

**重要 (上界・下界の符号)**:
- 出力密度 `f_q(y) = (p ∗ 𝒩(0,N))(y)` は **上に `1/√(2πN)` で有界** (各 component の sup を畳み込み積分が継承)。したがって `log f_q(y) ≤ −(1/2)log(2πN) < 0`、すなわち**上界は定数**。
- 下界は `f_q(y) ≥ 0` で `log f_q(y)` が下に非有界になりうるが、`f_q(y) ≥ ∫ 𝒩(y−x; N) ... ` の評価より `−log f_q(y)` が **二次オーダー `(y²/2N)+C` で押さえられる**ことを示す必要 (Gaussian の tail から)。`p` が有限二次モーメント (`∫x²∂p ≤ P`)、`q = p∗𝒩` も二次モーメント `≤ P+N` を持つので、`∫ |log f_q| ∂q ≤ ∫ (二次式) ∂q < ∞`。

### C. Var(Y) ≤ E[X²] + N の構成要素

| 概念 | Mathlib API | file:line | 状態 | 本壁での扱い |
|---|---|---|---|---|
| 独立和の分散加法性 | `ProbabilityTheory.IndepFun.variance_add` | `Mathlib/Probability/Moments/Variance.lean:406` | ✅ 既存 | `Var(X+Z) = Var(X) + Var(Z)` |
| 同上 (関数形) | `ProbabilityTheory.IndepFun.variance_fun_add` | `Variance.lean:416` | ✅ 既存 | `fun ω ↦ X ω + Y ω` 形 |
| 分散 ≤ 二次モーメント | `ProbabilityTheory.variance_le_expectation_sq` | `Variance.lean:340` | ✅ 既存 | `Var(X) ≤ E[X²]` |
| `Var = E[X²] − E[X]²` | `ProbabilityTheory.variance_def'` | `Variance.lean` (loogle 確認) | ✅ 既存 | 分散↔二次モーメント橋渡し |
| Gaussian の分散 = v | `ProbabilityTheory.variance_fun_id_gaussianReal` | `Gaussian/Real.lean:518` | ✅ 既存 | `Var(Z) = N` (`Z ∼ 𝒩(0,N)`) |
| 分散 = 積分形 (in-tree 利用例) | `ProbabilityTheory.variance_eq_integral` | `Mathlib/Probability/Moments/Variance.lean` (`AWGN.lean:215` で使用) | ✅ 既存 | `∫(x−m)²∂μ = Var` 変換 |
| `id ∈ L²(gaussianReal)` (in-tree) | `memLp_id_gaussianReal` | `ContChannelMIDecomp.lean:391` 内で使用 | ✅ 既存 | `MemLp X 2 μ` 前提供給 |

**`IndepFun.variance_add` の signature** (`Variance.lean:406` verbatim):

```lean
nonrec theorem IndepFun.variance_add {X Y : Ω → ℝ} (hX : MemLp X 2 μ)
    (hY : MemLp Y 2 μ) (h : X ⟂ᵢ[μ] Y) : Var[X + Y; μ] = Var[X; μ] + Var[Y; μ]
```
- section context: `variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}`。
- **`MemLp X 2 μ` (二乗可積分) を両辺要求**。AWGN では `X ∼ p` が `∫x²≤P` で `MemLp 2` を満たすか要確認 (`∫x²<∞ ⟹ MemLp 2` は成立、ただし `p` が一般測度なので bridge 補題が要る)。

**`variance_le_expectation_sq` の signature** (`Variance.lean:340` verbatim):

```lean
theorem variance_le_expectation_sq [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hm : AEStronglyMeasurable X μ) : variance X μ ≤ μ[X ^ 2]
```
- `[IsProbabilityMeasure μ]` 前提 (確率測度なので OK)。`μ[X^2] = ∫ X² ∂μ`。

### D. 既存の MI 上界 / DPI / variational 形 (別ルート可能性)

| 概念 | Mathlib API | file:line | 状態 | 本壁での扱い |
|---|---|---|---|---|
| `mutualInfo` 一般定義 | — (Mathlib に不在) | — | ❌ **不在** (loogle `ProbabilityTheory.mutualInfo` → 0、`shannon-mathlib-inventory.md` 既出) | 別ルート不可 |
| klDiv DPI / pushforward 単調性 | `klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν` | — | ❌ **不在** (loogle `InformationTheory.klDiv (Measure.map _ _) (Measure.map _ _)` → 0 match) | 別ルート不可 |
| klDiv 上界 (variational 形) | — | — | ❌ **不在** (loogle `InformationTheory.klDiv _ _, (_ ≤ _)` → `mul_log_le_klDiv` 等 **下界 (Pinsker)** のみ 3 件) | 別ルート不可 |
| klDiv chain rule (compProd 形) | `InformationTheory.klDiv_compProd_eq_add` | `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:204` | ✅ 既存 | 既に in-tree MI decomp で消費済 (再利用不要) |
| **in-tree MI = entropy 差分解** | `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` | `ContChannelMIDecomp.lean:276` | ✅ **既存 (genuine, 0 sorry, `@audit:ok`)** | **本壁の主役**。下記前提ボックス参照 |
| **in-tree Gaussian max-entropy** | `differentialEntropy_le_gaussian_of_variance_le` | `InformationTheory/Shannon/DifferentialEntropy.lean:520` | ✅ **既存 (4 hyp 形)** | **本壁の主役**。下記前提ボックス参照 |
| in-tree Gaussian 微分エントロピー閉形 | `differentialEntropy_gaussianReal` | `DifferentialEntropy.lean` (使用 `:162`) | ✅ 既存 | `h(𝒩(0,v)) = (1/2)log(2πev)`、fibre entropy 計算 |

**結論 D**: Mathlib には MI 上界・DPI・variational 形が一切無いため、converse を「MI を直接上から押さえる」別ルートで出すことは**不可能**。in-tree の entropy 差分解 (genuine 完成済) を経由する一本道。素材は B/C に揃っている。

---

## 主要前提条件ボックス (事故の起きやすい lemma)

### `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` (`ContChannelMIDecomp.lean:276`)
任意 `p` で適用するために供給が必要な引数 (verbatim):
- `(hW_ac : ∀ x, W x ≪ volume)` — AWGN fibre `𝒩(x,N) ≪ volume`。`gaussianReal_absolutelyContinuous` で OK。
- `(hWx_q : ∀ x, W x ≪ outputDistribution p W)` — fibre ≪ output。**一般 `p` では `q = p∗𝒩` が full-support Gaussian でないと自明でない**。`p∗𝒩` は全域正値 (Gaussian 畳み込み) なので成立するはずだが、in-tree の `awgnChannel_apply_absolutelyContinuous_output` (`:353`) は **`h_out : IsAwgnOutputGaussian` (= Gaussian 入力で出力が `𝒩(0,P+N)`) に依存**しており一般 `p` には使えない。**自作要**。
- `(hq_ac : outputDistribution p W ≪ volume)` — `Measure.conv_absolutelyContinuous` から。
- `(h_joint_ac : (p ⊗ₘ W) ≪ p.prod (outputDistribution p W))` — Bayes 密度分割の前提。
- `(g : ℝ × ℝ → ℝ≥0∞) (hg_meas : Measurable g)` + `(hg_ae : ∀ x, (W x).rnDeriv volume =ᵐ[W x] g(x, ·))` — Route B proxy。AWGN は `g := gaussianPDF` (`measurable_gaussianPDF_uncurry :370`) で供給可能。
- `(h_int_fibre : Integrable (fun z => log (g z).toReal) (p ⊗ₘ W))` — `integrable_log_gaussianPDFReal_gaussianReal` で fibre 側供給可。ただし `p` 上の積分 (`∫_x ∫_y log(g) ∂(W x) ∂p`) として閉じるには `p` 上の可積分性が要る → **fibre entropy が定数 `(1/2)log(2πeN)` なので `p` 確率測度で自動可積分**。
- **★ `(h_int_out : Integrable (fun z => log ((outputDistribution p W).rnDeriv volume z.2).toReal) (p ⊗ₘ W))`** — **これが本壁**。mixture 出力密度の log の可積分性。`q` 周辺化すれば `∫_y log(f_q(y)) ∂q` (B の評価)。

### `differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:520`)
verbatim signature:
```lean
theorem differentialEntropy_le_gaussian_of_variance_le
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (h_mean : ∫ x, x ∂μ = m)
    (h_var : ∫ x, (x - m)^2 ∂μ ≤ (v : ℝ))
    (h_var_int : Integrable (fun x => (x - m)^2) μ)
    (h_ent_int : Integrable
      (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) :
    differentialEntropy μ ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)
```
- `[IsProbabilityMeasure μ]` — `q` 確率測度で OK。
- **`(m : ℝ)` は explicit + `(h_mean : ∫ x ∂μ = m)`** — 任意の `m` ではなく**真の平均**を渡す必要。converse では `m := E[Y] = E[X]` (`Z` 平均 0)。`E[X]` が分からない一般 `p` でも `h_mean` で結びつくだけなので `m := ∫x∂q` を取れば自動。
- **`(h_var : ∫ (x−m)² ∂μ ≤ v)`** — これは `Var(Y) ≤ v`。converse では `v := (P+N).toNNReal` を取り、`Var(Y) = Var(X)+N ≤ E[X²]+N ≤ P+N` (C の素材)。**`m` を真の平均にしておかないと `∫(x−m)²` が分散にならない**点が落とし穴。
- **★ `(h_ent_int : Integrable (negMulLog (μ.rnDeriv volume)) volume)`** — **これが本壁 (`h_int_out` と本質同型)**。
- `(h_var_int : Integrable (fun x => (x−m)²) μ)` — `q = p∗𝒩` の二次モーメント有限性。`p` 二次モーメント有限 + `𝒩` 二次モーメント有限 → `q` 二次モーメント有限。`integrable_sq_sub_gaussianReal` は Gaussian 法則専用なので mixture 用に**自作 (薄い) 要**。

---

## 自作が必要な要素 (優先度順)

1. **`output_conv_eq` — `outputDistribution p W = p ∗ gaussianReal 0 N`** (任意 `p`)。
   - 推奨実装: `outputDistribution p W = (p⊗ₘW).snd = W ∘ₘ p` (`Measure.snd_compProd`) → `bind_eq_conv_of_translation_kernel` (in-tree `:78`) で `= p ∗ 𝒩(0,N)`。
   - 工数: ~15〜25 行。落とし穴: `W ∘ₘ p` の `∘ₘ` と `bind` の defeq、`Measure.snd_compProd` の引数順。

2. **`output_secondMoment_le` — `∫ y² ∂q ≤ P + N` & `Var(Y) ≤ P + N`** (`h_var` + `h_var_int` 供給)。
   - 推奨実装: `q = p∗𝒩` の二次モーメントを `IndepFun.variance_add` + `variance_le_expectation_sq` + `variance_fun_id_gaussianReal` で。`X ∼ p` の `MemLp 2` を `∫x²<∞` から導く bridge が要る (`memLp_two_iff_integrable_sq` 系)。
   - 工数: ~40〜60 行。落とし穴: `MemLp X 2 μ` を一般 `p` 入力で確立する部分、`m = E[Y]` の取り方。

3. **★ `output_logDensity_integrable` — `h_int_out` / `h_ent_int` (mixture 出力 log-density 可積分)**。【本壁の真の核心、唯一の Mathlib 不在】
   - 推奨実装: (a) `rnDeriv_conv` (加法形) で `f_q =ᵐ[vol] (p.rnDeriv vol) ⋆ₗ[vol] (𝒩.rnDeriv vol)` 構造を得る、もしくは (b) より直接に `f_q(y) = ∫ gaussianPDFReal x N y ∂p(x)`形 (`lconvolution_def` + `lintegral_conv`)。
     - 上界: `f_q(y) ≤ 1/√(2πN)` (自作補題 `gaussianPDFReal_le_sup`) ⟹ `log f_q ≤ const`。
     - 下界の二次優関数: `−log f_q(y) ≤ y²/(2N) + C`（Jensen / Gaussian tail）⟹ `|log f_q|` を `c₀ + c₁·y²` で押さえる。
     - `q` の二次モーメント有限 (#2) + `Integrable.mono'` で `Integrable (log f_q) q` ⟹ `h_int_out` (joint への lift は `integrable_map_measure` + `snd` marginal、in-tree `:329` 同型)。
   - 工数: **~80〜150 行** (本壁の大半)。落とし穴: 下界の二次評価が Jensen 経由で `negMulLog` の符号管理が煩雑。`negMulLog (f) = −f·log f` なので `f → 0` の端と `f` 上界の両側評価が要る。

4. **`fibre_absolutelyContinuous_output_general` — `∀ x, W x ≪ q`** (一般 `p`、`hWx_q` 供給)。
   - 推奨実装: `q = p∗𝒩(0,N)` は全域正値 (full support) なので `𝒩(x,N) ≪ q`。`q` の full-support を `lintegral_conv` の正値性から。
   - 工数: ~20〜30 行。落とし穴: in-tree `awgnChannel_apply_absolutelyContinuous_output` は Gaussian 入力専用、再利用不可。

5. **`gaussianPDFReal_le_sup` — `gaussianPDFReal m v y ≤ 1/√(2πv)`**。
   - 推奨実装: `gaussianPDFReal` の exp 因子 ≤ 1 から。
   - 工数: ~10 行。落とし穴: なし (#3 の素材)。

6. **算術ステップ** — `(1/2)log(2πe(P+N)) − (1/2)log(2πeN) = (1/2)log(1+P/N)`。
   - 推奨実装: in-tree `mutualInfoOfChannel_gaussianInput_closed_form` (`AWGN.lean:176-191`) の log 代数を流用。
   - 工数: ~20 行。落とし穴: なし (既存パターンのコピー)。

合計工数感: **~5〜6 本、200〜300 行**。#3 が支配的。

import 追加 (上記自作で新規に要るもの): `Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym` (`rnDeriv_conv`)、`Mathlib.Analysis.LConvolution` (`lconvolution_def`)、`Mathlib.MeasureTheory.Group.Convolution` (`conv` / `lintegral_conv` / `conv_absolutelyContinuous`)。Variance / Gaussian 系は既存 import 内。

---

## Mathlib 壁の列挙 (真に不在、`@residual(wall:...)` 対象)

| 壁 | loogle 確認 | 自作 self-derivable? | shared sorry 集約候補? |
|---|---|---|---|
| mixture-of-Gaussians 出力 log-density 可積分性 (`h_int_out` / `h_ent_int`) | `Integrable (fun _ => Real.log _) _` → **0 match**; `Integrable (fun _ => Real.negMulLog _) _` → **0**; `InformationTheory.klDiv (Measure.map _ _) ...` → 0 (DPI 経由も不可) | **Yes** (`rnDeriv_conv` + Gaussian pdf 上下界 + 二次モーメント有限で組める) | **強く推奨** — 隣接壁 `awgn-per-letter-integrability` (`AwgnWalls.lean:251`) が**同型の Mathlib gap** (`differentialEntropy_le_gaussian_of_variance_le` の `h_ent_int`、`DifferentialEntropy.lean:518` を明示参照、`AwgnWalls.lean:246-248`)。両者を **1 本の shared sorry 補題「Gaussian mixture (continuous or discrete) の log-density 可積分性」**に集約推奨 (`docs/audit/audit-tags.md`「共有 Mathlib 壁」)。**ただし regularity 前提を落とさないこと** (audit-tags.md 2026-05-28 `contChannelMIDecomp_holds` 教訓: over-general 化で偽になる) |
| MI 上界 / klDiv DPI / variational 形 | `InformationTheory.klDiv _ _, (_ ≤ _)` → 下界 (Pinsker) のみ; `mutualInfo` namespace → 0 | N/A (別ルート、本壁では不使用) | — |

**注**: 本壁 `awgn-capacity-converse-maxent` は厳密には「Mathlib 不在の hard wall」ではなく「self-derivable だが未実装」。`@residual(wall:...)` 分類は audit-tags register で正当 (登録済 `:75`)。ただし上記 #3 を埋めれば genuine 化できるので、長期 stuck な `wall:stam` 等とは性質が異なる (medium 深度)。

---

## 撤退ラインへの距離

親計画 `awgn-moonshot-plan.md` の撤退ライン:
- **F-3** `IsAwgnConverseHypothesis` (per-letter max-entropy `h_ent_int` を hyp 外出し → `awgn-converse-aux-plan.md` に defer) — **既に全採用済 (発動済、L:114-119)**。
- 自作 plumbing 肥大ライン **L-A1/L-A2/L-C1/L-D1** は moonshot 本体で未発動。

**判定: 本壁は既発動の F-3 の "下流" に位置し、新規撤退ラインは不要 (発動しない)**。
- F-3 は n-letter coding converse の per-letter `h_ent_int` を defer したもの。本壁は **single-letter capacity converse** (codebook-free `∀ p : Measure ℝ`) であり対象が別だが、Mathlib gap は同型 (Gaussian mixture log-density 可積分性)。
- したがって本壁の closure は「F-3 で defer した壁の本体を埋める」作業に相当し、撤退ではなく**前進**。
- **ただし #3 (output log-density 可積分性) が 1〜2 週間で書けない場合**の縮退案を新規撤退ラインとして提案:
  - **新撤退ライン L-CONV-1** — `h_int_out`/`h_ent_int` を `output_logDensity_integrable` shared sorry 補題 (`@residual(wall:awgn-capacity-converse-maxent` または新 `gaussian-mixture-log-integrability` に集約) として残し、`awgn_capacity_closed_form_of_out` の body は **その補題を呼び出す形に書換**えて signature を unconditional に保つ。capacity closed form の他の全ステップ (#1/#2/#4/#5/#6) は genuine 化。**仮説 bundling 禁止** — `h_int_out` を定理の hyp 引数に格上げするのは load-bearing になるので不可。撤退口は body 内 `have ... := shared_lemma` の `sorry` (補題側に集約)。

---

## 着手 skeleton

`InformationTheory/Draft/Shannon/AwgnCapacityConverseMaxent.lean` の出だし (新規 file 想定。既存 `ContChannelMIDecomp.lean` 内 helper として書く案もある):

```lean
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.LConvolution
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Gaussian.Real
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.ChannelCoding
import InformationTheory.Shannon.AWGN
import InformationTheory.Shannon.AWGNBindConvBody
import InformationTheory.Draft.Shannon.ContChannelMIDecomp

namespace InformationTheory.Shannon.AWGN

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Topology

variable {P : ℝ} {N : ℝ≥0}

/-- (#1) 任意入力 `p` での AWGN 出力は noise との畳み込み `p ∗ 𝒩(0,N)`. -/
theorem outputDistribution_awgn_eq_conv
    (h_meas : IsAwgnChannelMeasurable N) (p : Measure ℝ) [SFinite p] :
    ChannelCoding.outputDistribution p (awgnChannel N h_meas)
      = p ∗ gaussianReal 0 N := by
  sorry  -- @residual(wall:awgn-capacity-converse-maxent)

/-- (#5) Gaussian pdf の sup 上界 `≤ 1/√(2πv)`. -/
theorem gaussianPDFReal_le_sup (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (y : ℝ) :
    gaussianPDFReal m v y ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  sorry  -- @residual(wall:awgn-capacity-converse-maxent)

/-- (#3, ★ 本壁) 連続 mixture 出力 `p ∗ 𝒩(0,N)` の log-density は可積分. -/
theorem outputDistribution_logDensity_integrable
    (h_meas : IsAwgnChannelMeasurable N) (p : Measure ℝ) [IsProbabilityMeasure p]
    (hp_2mom : ∫ x, x^2 ∂p ≤ P) :
    Integrable (fun y : ℝ =>
        Real.negMulLog
          ((ChannelCoding.outputDistribution p (awgnChannel N h_meas)).rnDeriv
            volume y).toReal)
      volume := by
  sorry  -- @residual(wall:awgn-capacity-converse-maxent) — shared sorry 集約候補

/-- 本壁の最終結論 (`awgn_capacity_closed_form_of_out` の `h_max_ent` を供給). -/
theorem awgn_per_input_mi_le_log
    (hP : 0 < P) (hN : (N : ℝ) ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    (p : Measure ℝ) [IsProbabilityMeasure p] (hp_2mom : ∫ x, x^2 ∂p ≤ P) :
    (ChannelCoding.mutualInfoOfChannel p (awgnChannel N h_meas)).toReal
      ≤ (1/2) * Real.log (1 + P / (N : ℝ)) := by
  sorry  -- @residual(wall:awgn-capacity-converse-maxent)

end InformationTheory.Shannon.AWGN
```

---

## まとめ

- インベントリ: **`docs/shannon/awgn-capacity-converse-maxent-inventory.md`** (本ファイル)
- 主役 2 本 (`mutualInfoOfChannel_toReal_eq_diffEntropy_sub` genuine 完成 + `differentialEntropy_le_gaussian_of_variance_le` 既存) は in-tree。素材 (畳み込み rnDeriv / variance 加法 / Gaussian pdf) は Mathlib にほぼ完備。
- **既存率: 主役 API 100%、補助素材 ~90%** (Gaussian pdf 上界のみ自作)。**真の Mathlib 不在は 1 件 (mixture log-density 可積分性、self-derivable)**。
- 自作: **5〜6 本 / 200〜300 行**、うち #3 (output log-density 可積分性、~80〜150 行) が支配的。
- 撤退ライン: 親計画 F-3 の下流。**新規撤退ライン発動: no** (前進方向)。#3 が書けない場合の縮退案 L-CONV-1 (shared sorry 補題化、仮説 bundling 禁止) を提案として記載。
- shared sorry 集約: 隣接壁 `awgn-per-letter-integrability` (`AwgnWalls.lean:251`) と同型 gap、**1 本に集約推奨** (regularity 前提を落とさない条件付き)。
