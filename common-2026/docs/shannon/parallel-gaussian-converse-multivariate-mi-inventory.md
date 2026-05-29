# ② parallel-gaussian converse — `wall:multivariate-mi` 独立再検証 + Mathlib/Common2026 在庫

> 対象: `Common2026/Shannon/ParallelGaussianPerCoordRegularity.lean:120` (`bddAbove` field) +
> `:127` (`max_ent` field)、両 `sorry` + `@residual(wall:multivariate-mi)`。
> achiever 側 (`achiever_mi`, :121-124) は genuine 化済。converse のみが残 residual。
> 親計画: `docs/shannon/parallel-gaussian-headline-honest-restructure-plan.md` / `parallel-gaussian-chain-rule-plan.md`。

## 一行サマリ

**converse 2 件 (`bddAbove` / `max_ent`) は「真の Mathlib 壁」ではなく self-buildable。**
必要部品の **既存率 ~70%**: 1-D converse template (`awgn_per_input_mi_le_log`, `@audit:ok`) + Gaussian
max-entropy (`differentialEntropy_le_gaussian_of_variance_le`, `@audit:ok`) + n-変量 subadditivity
(`jointDifferentialEntropyPi_le_sum`, genuine) + per-fibre rnDeriv split の generic 核
(`rnDeriv_compProd_fibre`, generic `{α β}`) が全て既存。自作必要 = **4 件** (うち最大は「1-D channel↔RV decomp の `Fin n → ℝ` lift」)。
**撤退ライン発動: NO** (converse は staged 退避でなく genuine 着地可能、推定 ~180-260 行)。
**最も危険な発見**: 1-D decomp body (`mutualInfoOfChannel_toReal_eq_diffEntropy_sub`) は `Measure ℝ` / `Channel ℝ ℝ` / `differentialEntropy` (1-D) に**ハードワイヤ**されており、generic 再インスタンス化では lift できない (`differentialEntropy : Measure ℝ → ℝ` ≠ `jointDifferentialEntropyPi`)。lift は新規 decl の自作になる (詳細 §B / §E)。

---

## 主定理の最終形（再掲）

`ParallelGaussianPerCoordRegularity.lean:108-127`、converse 側 2 field:

```lean
-- bddAbove (:115/:118-120):
BddAbove (miImage P N h_meas h_parallel_meas)
-- max_ent (:117/:125-127):  -- IsParallelGaussianPerCoordRegularity.max_ent の field 型 (PerCoord.lean:205-209)
∀ p ∈ parallelGaussianPowerConstraintSet P,
  ∃ P' : Fin n → ℝ, (∀ i, 0 ≤ P' i) ∧ (∑ i : Fin n, P' i ≤ P) ∧
    (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
      ≤ ∑ i : Fin n, (1/2) * Real.log (1 + P' i / (N i : ℝ))
```

数学的 converse の証明戦略 (1-D `awgn_per_input_mi_le_log` の n-変量化、pseudo-Lean):

```
-- 任意の feasible (correlated) p に対し:
I(p; parallelChan).toReal
  = h(Yⁿ) − ∫ h_fibre(W x) ∂p           -- (★1) channel↔RV decomp の Fin n lift  [自作 #1]
  = jointDiffEntropyPi(μ_Y) − ∫ ... ∂p   --     (output joint entropy − fibre entropy)
  ≤ ∑ᵢ h(Yᵢ) − ∫ ... ∂p                  -- jointDifferentialEntropyPi_le_sum (既存 genuine)
  ≤ ∑ᵢ [(1/2)log(2πe·Var(Yᵢ)) − h(Zᵢ)]   -- per-coord Gaussian max-entropy (既存 1-D)  + fibre = (1/2)log(2πe·Nᵢ)
  ≤ ∑ᵢ (1/2)log(1 + P'ᵢ/Nᵢ)              -- log-algebra (1-D template と同一)
-- bddAbove は上記 RHS が p に依らない定数上界 → 自明に BddAbove          [自作 #4]
```

`parallelGaussian_max_ent_le_of_subadditivity` (`PerCoord.lean:293`) は既にこの戦略の中核
(`jointDifferentialEntropyPi_le_sum` を呼ぶ部分) を genuine 実装済。残るのは `h_decomp` (★1) と
`h_perCoord` (per-coord max-ent) を **honest hypothesis でなく実値で供給**すること。

---

## A. `parallelGaussian_max_ent_le_of_subadditivity` 全 hyp 分類表

`Common2026/Draft/Shannon/ParallelGaussianPerCoord.lean:293-328`。各引数 verbatim:

| # | 引数 (verbatim) | 種別 | 備考 / 供給元 |
|---|---|---|---|
| inst | `[IsProbabilityMeasure μY]` | regularity precondition | 出力法は Markov channel ⇒ prob measure。genuine 自動 |
| inst | `[∀ i, IsProbabilityMeasure (μY.map (fun z => z i))]` | regularity precondition | marginal も prob。genuine |
| arg | `(miReal condTerm : ℝ) (P' : Fin n → ℝ) (N : Fin n → ℝ≥0)` | data | — |
| **h_decomp** | `(h_decomp : miReal = jointDifferentialEntropyPi μY - condTerm)` | **★ load-bearing (核心 1)** | channel↔RV MI decomp `I = h(Yⁿ) − condTerm`。**現状 honest hyp。これが残 wall の本体** → §B |
| h_marg_ac | `(h_marg_ac : ∀ i, (μY.map (fun z => z i)) ≪ volume)` | regularity precondition | Gaussian conv 出力 ⇒ AC。genuine、§D |
| hμ_ac | `(hμ_ac : μY ≪ (volume : Measure (Fin n → ℝ)))` | regularity precondition | 同上。§D |
| h_joint_ac | `(h_joint_ac : μY ≪ Measure.pi (fun i => μY.map (fun z => z i)))` | regularity precondition | joint ≪ ∏marginal。**correlated 入力では非自明** → §D |
| h_int_marg | `(h_int_marg : ∀ i, Integrable (fun z => Real.log (((μY.map (fun z => z i)).rnDeriv volume (z i)).toReal)) μY)` | regularity precondition (integrability) | §D |
| h_int_joint | `(h_int_joint : Integrable (fun z => Real.log ((μY.rnDeriv volume z).toReal)) μY)` | regularity precondition (integrability) | §D |
| **h_perCoord** | `(h_perCoord : (∑ i, differentialEntropy (μY.map (fun z => z i))) - condTerm ≤ ∑ i, (1/2) * Real.log (1 + P' i / (N i : ℝ)))` | **★ load-bearing (核心 2)** | per-coord max-entropy + variance allocation。**現状 honest hyp** → §C |
| 結論 | `miReal ≤ ∑ i, (1/2) * Real.log (1 + P' i / (N i : ℝ))` | — | — |

**body (`:313-328`) 内部**: `jointDifferentialEntropyPi_le_sum` (genuine、subadditivity) を呼び、`h_decomp` + `h_perCoord` + subadditivity を `linarith` で組む。
→ **subadditivity 自体は壁でない (genuine)**。残 load-bearing は厳密に **2 件のみ: `h_decomp` (§B) と `h_perCoord` (§C)**。regularity 6 件 (§D) は precondition なので壁でなく供給作業。

---

## B. `h_decomp` (channel↔RV MI decomp) の lift 在庫 ★最重要

### 既存 1-D version (genuine, `@audit:ok`)

`Common2026/Draft/Shannon/ContChannelMIDecomp.lean:276-289`、verbatim:

```lean
variable {p : Measure ℝ} [IsProbabilityMeasure p]            -- :64
variable {W : Channel ℝ ℝ} [IsMarkovKernel W]                -- :65
theorem mutualInfoOfChannel_toReal_eq_diffEntropy_sub
    (hW_ac : ∀ x, W x ≪ volume)
    (hWx_q : ∀ x, W x ≪ outputDistribution p W)
    (hq_ac : outputDistribution p W ≪ volume)
    (h_joint_ac : (p ⊗ₘ W) ≪ p.prod (outputDistribution p W))
    (g : ℝ × ℝ → ℝ≥0∞) (hg_meas : Measurable g)
    (hg_ae : ∀ x, (fun y => (W x).rnDeriv volume y) =ᵐ[W x] fun y => g (x, y))
    (h_int_fibre : Integrable (fun z : ℝ × ℝ => Real.log (g z).toReal) (p ⊗ₘ W))
    (h_int_out : Integrable
        (fun z : ℝ × ℝ => Real.log
            ((outputDistribution p W).rnDeriv volume z.2).toReal) (p ⊗ₘ W)) :
    (mutualInfoOfChannel p W).toReal
      = Common2026.Shannon.differentialEntropy (outputDistribution p W)
        - (∫ x, Common2026.Shannon.differentialEntropy (W x) ∂p)
```

### lift 可能性評価 (verbatim body 確認済)

**結論: generic 再インスタンス化では lift 不可。新規 decl の自作が必要 (~80-120 行)。**

| 部品 | file:line | 現状 generic 性 | lift 必要作業 |
|---|---|---|---|
| `mutualInfoOfChannel` (def) | `ChannelCoding.lean:85` | **generic** `(p : Measure α) (W : Channel α β)` | そのまま `α = β = (Fin n → ℝ)` |
| `outputDistribution` (def) | `ChannelCoding.lean:72` | **generic** | そのまま |
| `toReal_klDiv_of_measure_eq` | (ContChannelMIDecomp 内 callee) | generic 推定 (KL は任意可測空間) | 要確認、おそらく generic |
| `rnDeriv_compProd_fibre` | `ContChannelMIDecomp.lean:142-149` | **fully generic** `{α β} [CountableOrCountablyGenerated α β] {μ} {κ η} [IsFiniteMeasure] [IsFiniteKernel]` | `α = β = (Fin n → ℝ)` で `CountableOrCountablyGenerated` instance 要確認 (標準 Borel 系で成立見込み) |
| `log_rnDeriv_split` | `ContChannelMIDecomp.lean:171-173` | **ℝ-specific** `{ν q : Measure ℝ}` | `Measure (Fin n → ℝ)` へ一般化 (body は `volume` / `rnDeriv` の generic 性質のみ使用 → 機械的、~15 行) |
| `llr_compProd_prod_split` | `ContChannelMIDecomp.lean:206-214` | **ℝ-specific** `q : Measure ℝ`, `g : ℝ × ℝ → ℝ≥0∞` | `Fin n → ℝ` 版自作 (~30 行、`log_rnDeriv_split` lift 後は機械的) |
| `integral_log_rnDeriv_eq_neg_diffEntropy` | `ContChannelMIDecomp.lean:85-88` | **ℝ-specific** (返り値 `differentialEntropy`) | **`jointDifferentialEntropyPi` 版を新規** (`MultivariateDiffEntropy.lean:86 integral_log_rnDeriv_self_eq_neg` が既に generic `{α}` なのでこれを再利用、~10 行) |
| body 全体 (`:290-329`) | ContChannelMIDecomp | ℝ-hardwire | `Fin n → ℝ` 版 theorem を新規記述、上記部品で組む (~40 行) |

**核心リスク**: 結論型の entropy が `differentialEntropy (1-D)` → `jointDifferentialEntropyPi` と
`∫ x, jointDifferentialEntropyPi (W x) ∂p` に変わる。`differentialEntropy` (`DifferentialEntropy.lean:45`,
`Measure ℝ → ℝ`) と `jointDifferentialEntropyPi` (`MultivariateDiffEntropy.lean:77`,
`Measure (Fin n → ℝ) → ℝ`) は**別 def** (型が違う)。ただし両者とも本体は
`∫ z, negMulLog ((μ.rnDeriv volume z).toReal) ∂volume` で**構造同一**であり、generic 核
`integral_log_rnDeriv_self_eq_neg` (`{α} [SigmaFinite] [HaveLebesgueDecomposition]`) が両方に適用可能。
→ lift は「型を `Fin n → ℝ` に書き換え + generic 核を再利用」で機械的に通る見込み。fibre 側
`∫ x, jointDifferentialEntropyPi (W x) ∂p` は parallel channel fibre `W x = Measure.pi (gaussianReal (x i)(N i))` が**積測度**なので、さらに `jointDifferentialEntropyPi (Measure.pi ...) = ∑ᵢ differentialEntropy (gaussianReal ...)` (積→和) の補題が要る (per-coord max-ent §C で消費)。

**助言者前評価 ~60-90 行 → 実評価 ~80-120 行** (decomp lift 単体)。generic 核が既にあるので
過小評価ではないが、`CountableOrCountablyGenerated (Fin n → ℝ)` instance の有無が 1 turn リスク。

---

## C. per-coord max-entropy 在庫 (`h_perCoord` の実値供給)

### 既存 Gaussian max-entropy (genuine, `@audit:ok`)

`Common2026/Shannon/DifferentialEntropy.lean:520-528`、verbatim:

```lean
@[entry_point]
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

これは **per-coordinate に直接適用可能** (各 marginal `μY.map (· i)` は `Measure ℝ`)。
`Fin n` 全 coord は `Finset.sum_le_sum` で束ねる。

### 1-D converse template (per-coord 適用の完全手本、genuine `@audit:ok`)

`Common2026/Draft/Shannon/AwgnCapacityConverseMaxent.lean:742-829` `awgn_per_input_mi_le_log`。
これは **§B の 1-D decomp + §C max-ent + fibre 定数 + Var(Y)≤P+N + log-algebra を組んだ完成 converse**。
verbatim 結論:

```lean
theorem awgn_per_input_mi_le_log
    (hP : 0 < P) (hN : (N : ℝ) ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    (p : Measure ℝ) [IsProbabilityMeasure p] (hp : p ∈ awgnPowerConstraintSet P) :
    (ChannelCoding.mutualInfoOfChannel p (awgnChannel N h_meas)).toReal
      ≤ (1/2) * Real.log (1 + P / (N : ℝ))
```

n-変量 per-coord max-ent は、各 coord `i` で `awgn_per_input_mi_le_log` の STEP 1-3
(`:792-829`) を再演すれば良い。fibre entropy 定数 `(1/2)log(2πe·Nᵢ)` は
`differentialEntropy_gaussianReal` (`DifferentialEntropy.lean` 内、`awgn` body `:806` で使用) で genuine。
**per-coord max-ent 自作規模 ~50-80 行** (1-D の STEP 構造を `Fin n` で sum + variance allocation `P'ᵢ`)。

| 部品 | file:line | 用途 |
|---|---|---|
| `differentialEntropy_le_gaussian_of_variance_le` | `DifferentialEntropy.lean:520` | 各 marginal の max-ent 上界 |
| `differentialEntropy_gaussianReal` | `DifferentialEntropy.lean` (`:806` で参照) | fibre `h(Zᵢ) = (1/2)log(2πe·Nᵢ)` 定数 |
| `awgn_per_input_mi_le_log` (1-D 完成形) | `AwgnCapacityConverseMaxent.lean:742` | log-algebra + 全体組立の手本 |
| variance allocation `P'ᵢ := Var(Yᵢ) − Nᵢ` | — | 自作 (各 coord で `∑P'ᵢ ≤ P` を `∑Var(Yᵢ) ≤ P+∑Nᵢ` から、相関でも total 2nd moment は sum で立つ) |

---

## D. correlated-input output regularity (regularity precondition 群の供給)

§A の 6 件 regularity hyp (`h_marg_ac` / `hμ_ac` / `h_joint_ac` / `h_int_marg` / `h_int_joint`) を
**相関入力 `p`** の出力法 `μY := outputDistribution p (parallelGaussianChannel N)` で genuine に立てる必要。
achiever の product 入力 factorization は使えない (correlated)。

| precondition | 相関入力で成立するか | 既存補題 / 自作規模 |
|---|---|---|
| `hμ_ac : μY ≪ volume` | **YES** (各 fibre Gaussian conv ⇒ 出力 AC) | 1-D `Measure.conv_absolutelyContinuous` (`AwgnCapacityConverseMaxent.lean:763` で使用) の n-変量版。parallel fibre = `Measure.pi (gaussianReal (x i)(N i))` なので `Measure.pi` の AC 補題 + conv。自作 ~20 行 |
| `h_marg_ac : ∀ i, μY.map(· i) ≪ volume` | **YES** | marginal も Gaussian 平滑化 ⇒ AC。push-forward + 1-D conv AC。~15 行 |
| `h_joint_ac : μY ≪ Measure.pi (marginals)` | **要注意** | **correlated 入力では joint ≠ ∏marginal が一般。だが AC `≪` は density 比が有界でなくても成立しうる。** Gaussian 平滑化で full-support ⇒ joint も ∏marginal も volume-equivalent ⇒ 相互 AC が立つ見込み (両方 volume と相互 AC なら推移)。要 verbatim 確認だが genuine 可能性高。~25 行 |
| `h_int_marg` / `h_int_joint` (log-density integrability) | **YES (規模あり)** | 1-D は `outputDistribution_logDensity_integrable[_joint]` (`AwgnCapacityConverseMaxent.lean:739, 791, 824` Phase 6) で genuine 供給。n-変量版が**最大の plumbing**。1-D Phase 6 が ~75 行だった (finiteness inventory より) ので、n-変量で ~60-100 行 |

**規模合計 (§D)**: ~120-160 行。最大単項は log-density integrability の n-変量化。
ただし 1-D Phase 6 が既に genuine 完成形 (`@audit:ok`) なので、構造模倣で過小評価リスクは中程度。

---

## E. 規模見積もり (3 段階) — sub-piece 別

| sub-piece | self-buildable? | 既存基盤 | 自作規模 |
|---|---|---|---|
| **#1 `h_decomp` lift** (channel↔RV decomp `Fin n → ℝ`) | self-buildable | generic 核 `rnDeriv_compProd_fibre` / `integral_log_rnDeriv_self_eq_neg` + 1-D body 手本 | **~80-120 行** |
| **#2 per-coord max-ent** (`h_perCoord` 実値) | self-buildable | `differentialEntropy_le_gaussian_of_variance_le` + 1-D `awgn_per_input_mi_le_log` 手本 + variance allocation | **~50-80 行** |
| **#3 correlated output regularity** (§A 6 hyp) | self-buildable | 1-D conv AC + Phase 6 integrability 手本 | **~120-160 行** |
| **#4 `bddAbove` field** | self-buildable (#2 に従属) | #2 の RHS が p-非依存定数上界 → `BddAbove` 自明 | **~15-30 行** (#1#2#3 完成後) |
| **組立** (`max_ent` field を `parallelGaussian_max_ent_le_of_subadditivity` 経由で埋める) | self-buildable | wrapper は既存 (`PerCoord.lean:293`) | **~20-40 行** |
| **合計** | — | — | **~285-430 行** |

> 注: §B の lift (#1) と §C (#2) は 1-D の `awgn_per_input_mi_le_log` が**両方を 1 theorem に統合した完成形** (`@audit:ok`) として存在する。n-変量化は「1-D を Fin n に持ち上げる」機械的作業が主体で、新規数学はゼロ (subadditivity + Gaussian max-ent + chain rule は全て既存 genuine)。

---

## 判定: **self-buildable** (真の Mathlib 壁ではない)

- **`wall:multivariate-mi` は誤分類気味**: Mathlib に continuous channel MI decomp が無い (loogle `ProbabilityTheory.mutualInfo` / `MeasureTheory.condEntropy` = unknown identifier、Common2026 が全て自前) のは事実だが、**Common2026 側に 1-D genuine 完成形が既に揃っており**、converse は「1-D template の `Fin n` lift」で genuine 着地可能。"hard wall" でなく "big (規模)" 側。
- **regularity 6 件は壁でなく precondition** (§D)。correlated 入力でも Gaussian 平滑化 full-support により genuine に立つ見込み (`h_joint_ac` のみ 1 turn 確認リスク)。
- **最大の構造リスク**: §B の 1-D decomp body が `Measure ℝ` ハードワイヤ。generic 再インスタンス化では不可、新規 decl 自作。ただし依存核 (`rnDeriv_compProd_fibre`, `integral_log_rnDeriv_self_eq_neg`) は既に generic `{α}` なので lift は機械的。

### 真の wall 残量 (`@residual(wall:multivariate-mi)` 維持対象)

なし (full closure 可能の見込み)。loogle 確認:
- `MeasureTheory.condEntropy` → `unknown identifier` (Mathlib 不在、Common2026 自前)
- `ProbabilityTheory.mutualInfo` → `unknown identifier` (同上)
→ Mathlib 側 high-level MI/entropy API は不在だが、**Common2026 が必要部品を全て genuine 保有**するため、self-build で wall を消せる。**shared sorry 補題化は不要** (新規 wall は生じない)。

### 撤退ラインへの距離

親計画 `parallel-gaussian-headline-honest-restructure-plan.md` M0 の wall 認定は
「correlated 入力 converse = multivariate MI additivity wall、achiever product closure では閉じない」。
本再検証は **wall 認定を覆さない** (achiever では確かに閉じない) が、**converse 単独で self-build 可能**と判定。
→ **撤退ライン発動 NO**。縮退案不要。新規撤退ライン提案: 「§B #1 (decomp lift) で
`CountableOrCountablyGenerated (Fin n → ℝ)` instance が見つからない場合のみ、当該 1 件を
`sorry` + `@residual(wall:multivariate-mi)` で staged 維持 (他 3 piece は genuine 着地)」。

---

## F. 退化境界 (verbatim 確認済)

CLAUDE.md「具体的数値・型予測の verbatim 確認」に従い、相関入力の degenerate case を確認:

- **`gaussianReal μ 0 = Measure.dirac μ`** (Mathlib `Distributions/Gaussian/Real.lean:207`
  `gaussianReal_zero_var`, verbatim `:= if_pos rfl`)。
  → ノイズ `N i = 0` の座標は fibre が Dirac (退化)。だが headline `parallel_gaussian_capacity_formula_minimal`
  は `hN : ∀ i, (N i : ℝ) ≠ 0` を要求 (`ParallelGaussianPerCoordRegularity.lean:163`)、
  constructor も `hN` を取る (`:109`)。**全座標 `N i ≠ 0`** が precondition なので fibre Dirac は発生しない。
  max-ent 補題 `differentialEntropy_le_gaussian_of_variance_le` も `hv : v ≠ 0` を要求 → 整合。
- **入力 `P = 0`**: constraint `∑ᵢ ∫⁻ ofReal((xᵢ)²) ≤ ofReal 0` ⇒ 各座標 2nd moment 0 ⇒ 入力 Dirac at 0。
  converse RHS `∑ᵢ (1/2)log(1+P'ᵢ/Nᵢ)` で `P'ᵢ = 0` ⇒ `log 1 = 0` ⇒ RHS = 0。
  MI は入力決定論で `I = 0` (`≤ 0` で成立)。**converse 不等式は壊れない** (両辺 0)。
  ただし headline は `hP : 0 < P` (`:163`) を要求 ⇒ `P = 0` は headline scope 外。constructor 単体
  (`isParallelGaussianPerCoordRegularity_of_pieces`) は `P : ℝ` 無制約 (`:108`) なので、
  **`max_ent` field を埋める際は `P = 0` / 負の `P` でも `parallelGaussianPowerConstraintSet P` が
  空 (または Dirac のみ) になり vacuous/trivial に成立**することを確認すべき (退化定義悪用 tier-5 を避ける:
  RHS が trivially 成立する `P < 0` で exfalso する誘惑に注意。CLAUDE.md「退化定義の悪用」)。
- **相関で分散 0 の座標**: 入力 `p` の座標 `i` marginal が Dirac でも、出力 `Yᵢ = Xᵢ + Zᵢ` は
  `Zᵢ ∼ 𝒩(0,Nᵢ)` (`Nᵢ ≠ 0`) との conv ⇒ full-support Gaussian-smoothed ⇒ AC genuine
  (§D `h_marg_ac` 成立)。**出力側で退化しない** (ノイズが必ず平滑化)。

---

## 推奨着手順序

1. **#3 correlated output regularity (§D)** — 先に regularity 6 件を genuine 供給 (1-D conv AC +
   Phase 6 integrability の n-変量模倣)。これが無いと #1 の decomp が呼べない。最大 plumbing なので先行。
2. **#1 `h_decomp` lift (§B)** — `log_rnDeriv_split` / `llr_compProd_prod_split` /
   `integral_log_rnDeriv_eq_neg_diffEntropy` を `Fin n → ℝ` 一般化 → decomp body 新規 theorem。
   `CountableOrCountablyGenerated (Fin n → ℝ)` instance を最初に確認 (loogle/infer_instance)。
3. **#2 per-coord max-ent (§C)** — `differentialEntropy_le_gaussian_of_variance_le` を各 coord 適用 +
   variance allocation `P'ᵢ`。1-D `awgn_per_input_mi_le_log` STEP 1-3 を sum 化。
4. **組立 (`max_ent` field)** — `parallelGaussian_max_ent_le_of_subadditivity` (`PerCoord.lean:293`) を
   #1 (`h_decomp`) + #2 (`h_perCoord`) + #3 (regularity) で呼び、constructor `:127` の sorry を埋める。
5. **#4 `bddAbove` field (`:120`)** — #2 完成後、RHS が p-非依存定数上界 ⇒ `BddAbove` 自明に。

各段は独立 `lake env lean` 検証可。1→2→3 は依存連鎖、4→5 は前段完成後。

---

## 着手 skeleton

`Common2026/Shannon/ParallelGaussianConverse.lean` (新規、または `ParallelGaussianPerCoordRegularity.lean` 拡張):

```lean
import Common2026.Meta.EntryPoint
import Common2026.Shannon.ParallelGaussian
import Common2026.Draft.Shannon.ParallelGaussianPerCoord
import Common2026.Draft.Shannon.ContChannelMIDecomp     -- 1-D decomp 部品 (generic 核 reuse)
import Common2026.Draft.Shannon.MultivariateDiffEntropy -- jointDifferentialEntropyPi + subadditivity
import Common2026.Shannon.DifferentialEntropy           -- differentialEntropy_le_gaussian_of_variance_le
import Common2026.Draft.Shannon.AwgnCapacityConverseMaxent  -- 1-D converse 手本
import Mathlib.MeasureTheory.Constructions.Pi

namespace InformationTheory.Shannon.ParallelGaussian

open MeasureTheory ProbabilityTheory InformationTheory
open InformationTheory.Shannon.ChannelCoding
open Common2026.Shannon
open scoped ENNReal NNReal BigOperators

variable {n : ℕ} (P : ℝ) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
variable (h_meas : IsParallelAwgnChannelMeasurable N)
variable (h_parallel_meas : IsParallelGaussianKernelMeasurable N)

/-- #1 channel↔RV MI decomp, `Fin n → ℝ` lift. (§B) -/
theorem parallel_mutualInfoOfChannel_toReal_eq_diffEntropyPi_sub
    (p : Measure (Fin n → ℝ)) [IsProbabilityMeasure p]
    (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
      = jointDifferentialEntropyPi
          (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas))
        - ∫ x, jointDifferentialEntropyPi
            ((parallelGaussianChannel N h_meas h_parallel_meas) x) ∂p := by
  sorry -- @residual(plan:parallel-gaussian-converse) — decomp lift (§B #1)

/-- #2 per-coord max-entropy converse split (correlated input). (§C) -/
theorem parallel_per_input_mi_le_sum
    (p : Measure (Fin n → ℝ)) [IsProbabilityMeasure p]
    (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    ∃ P' : Fin n → ℝ, (∀ i, 0 ≤ P' i) ∧ (∑ i, P' i ≤ P) ∧
      (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
        ≤ ∑ i, (1/2) * Real.log (1 + P' i / (N i : ℝ)) := by
  sorry -- @residual(plan:parallel-gaussian-converse) — uses #1 + max-ent + subadditivity (§C)

end InformationTheory.Shannon.ParallelGaussian
```

> 注: `@residual` class は実装 plan 確定後 `plan:<slug>` に。現状 `wall:multivariate-mi` は self-build
> 判定により誤分類 (本 inventory の結論)。staged 維持が必要なのは §B #1 で
> `CountableOrCountablyGenerated (Fin n → ℝ)` が立たない場合の 1 件のみ。
```
