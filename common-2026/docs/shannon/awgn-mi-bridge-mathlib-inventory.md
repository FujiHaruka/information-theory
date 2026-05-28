# AWGN per-letter MI bridge — Mathlib API 在庫調査

> 発注元: `docs/shannon/awgn-mi-bridge-plan.md`（stub の TODO「`differentialEntropy` の Mathlib 対応物 inventory を先行依頼」）。
> 対象 sorry: `Common2026/Shannon/AWGNConverse.lean:86-93` の `awgn_converse` body 内 `h_mi_bridge_per_letter`（`@residual(plan:awgn-mi-bridge-plan)`）。
> Created: 2026-05-28。

## 一行サマリ

**bridge を構成する道具のうち実体（Bochner 積分・klDiv chain rule・rnDeriv・Gaussian PDF）はほぼ 100% Mathlib + Common2026 既存。だが「連続版 MI = `h(Y) − h(Y|X)`（density-level chain rule）」という結論形そのものは Mathlib 不在で、これが唯一の真の壁（既存率: 部品 ~90% / 結論形 0%）。** 自作必要は実質 1 件（連続 MI chain rule 補題）＋ per-letter mixture を `compProd` 形に乗せる橋渡し 1 件。撤退ライン発動: **No**（既存 `wall:awgn-mi-decomp` の枠内）。**最大の surprise: この壁は本 task 専用ではなく、`AWGNMIDecompBody.lean` の `IsContChannelMIDecompHyp`（load-bearing predicate、tier 4）として既に別経路で「Mathlib 不在」と判定済み — shared sorry 補題への集約が強く推奨される。**

---

## 主定理の最終形（再掲）

`Common2026/Shannon/AWGNConverse.lean:86-93`（body 内 honest residual）:

```lean
have h_mi_bridge_per_letter :
    ∀ {M n : ℕ} [NeZero M] (_hM : 2 ≤ M) (c : AwgnCode M n P), ∀ i : Fin n,
      (perLetterMI h_meas c i).toReal
        = Common2026.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
          - Common2026.Shannon.differentialEntropy
              (ProbabilityTheory.gaussianReal 0 N) := by
  sorry  -- @residual(plan:awgn-mi-bridge-plan)
```

ここで（verbatim 確認済）:
- `perLetterMI h_meas c i := mutualInfo (awgnConverseJoint h_meas c) (fun ω => c.encoder ω.1 i) (fun ω => ω.2 i)` (`AWGNConverseDischarge.lean:115`)。`mutualInfo` は `klDiv (μ.map (X,Y)) ((μ.map X).prod (μ.map Y))`（`MutualInfo.lean:37`）。
- `perLetterYLaw h_meas c i := (awgnConverseJoint h_meas c).map (fun ω => ω.2 i)` (`AWGNConverseDischarge.lean:108`) = **mixture of Gaussians** `(1/M) ∑ₘ 𝒩(c.encoder m i, N)`（closed form: `perLetterYLaw_eq_mixture` `AWGNConverseDischarge.lean:563`）。
- `differentialEntropy μ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume` (`DifferentialEntropy.lean:45`)。

証明戦略（pseudo-Lean、density-level chain rule）:

```text
I(X_i; Y_i) = KL( P_{X_i,Y_i} ‖ P_{X_i} ⊗ P_{Y_i} )
  -- (1) factor joint as p_i ⊗ₘ κ で κ = AWGN kernel, p_i = X_i marginal
  = klDiv (p_i ⊗ₘ κ) (p_i ⊗ₘ q_i)         -- q_i = P_{Y_i} marginal (Mathlib klDiv_compProd_eq_add の右第二項)
  = ∫∫ κ(y|x) log(κ(y|x)/q_i(y)) dy dp_i(x) -- density 展開 (klDiv → ∫ llr, rnDeriv Bayes split)
  = ∫∫ κ(y|x) log κ(y|x) dy dp_i(x)  −  ∫ q_i(y) log q_i(y) dy
  = − ∫ h(κ x) dp_i(x)  +  h(Y_i)         -- differentialEntropy 定義に畳む
  = h(perLetterYLaw)  − ∫ h(𝒩(x,N)) dp_i  -- 出力 entropy − 条件 entropy
  = h(perLetterYLaw)  − h(𝒩(0,N))         -- 各 fibre h(𝒩(x,N)) = h(𝒩(0,N)) (mean 不変)
```

最終の「各 fibre `h(𝒩(x,N)) = h(𝒩(0,N))`」だけは **既に Common2026 で genuine 証明済**（`differentialEntropy_awgnChannel_apply_eq_noise` `AWGNMIBridge.lean:108`）。残りの (1)〜density 展開〜畳み込みが壁。

---

## API 在庫テーブル

### A. `differentialEntropy` の Mathlib 対応物（軸 1）

調査結論: **Mathlib に連続版 differential entropy の def は存在しない**（loogle `differentialEntropy` / `MeasureTheory.differentialEntropy` → `unknown identifier`）。Common2026 自前 def が唯一。Mathlib にある関連の primitive は以下。

| 概念 | Mathlib / Common2026 API | file:line | 状態 | bridge での扱い |
|---|---|---|---|---|
| 微分エントロピー def 本体 | `Common2026.Shannon.differentialEntropy (μ : Measure ℝ) : ℝ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume` | `DifferentialEntropy.lean:45` | ✅ Common2026 自前（Mathlib 不在） | bridge RHS の両項。density 形 `differentialEntropy_eq_integral_density` で `-∫ f log f` に展開できる |
| Mathlib 連続版 differential entropy | — | — | ❌ **Mathlib 不在**（loogle `Found 0` 相当、`unknown identifier 'differentialEntropy'`） | 自前 def を使い続ける一択 |
| `-x log x` 被積分関数 | `Real.negMulLog (x : ℝ) : ℝ := -x * Real.log x` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:164` | ✅ 既存 | 被積分関数。`negMulLog 0 = 0` で台の境界自動処理 |
| density 形書換 | `Common2026.Shannon.differentialEntropy_eq_integral_density {f : ℝ → ℝ} (hf : Measurable f) (hf_nn : ∀ x, 0 ≤ f x) (μ : Measure ℝ) (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) : differentialEntropy μ = -∫ x, f x * Real.log (f x) ∂volume` | `DifferentialEntropy.lean:65` | ✅ 既存 | chain rule density 展開を `differentialEntropy` 結論形に畳む出口 |
| Gaussian 値 | `Common2026.Shannon.differentialEntropy_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : differentialEntropy (gaussianReal m v) = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)` | `DifferentialEntropy.lean:414` | ✅ 既存 | `h(𝒩(0,N))` の数値化（下流 max-entropy 側で使用、bridge 自体では不要） |
| 平均不変性（AWGN fibre） | `differentialEntropy_awgnChannel_apply_eq_noise (N : ℝ≥0) (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N) (x : ℝ) : differentialEntropy ((awgnChannel N h_meas) x) = differentialEntropy (gaussianReal 0 N)` | `AWGNMIBridge.lean:108` | ✅ 既存（genuine） | **条件 entropy `∫ h(𝒩(x,N)) dp = h(𝒩(0,N))` の核**。fibre 毎の平均シフト不変を Mathlib 直結で証明済 |

判定（軸 1）: **NEGATIVE**（Mathlib に対応 def なし）／ ただし自前 def + 既存補題群で bridge の RHS 側はすべて表現可能。`differentialEntropy` を Mathlib 形に rewrite する選択肢は「Mathlib に rewrite 先が無い」ので消滅（→ 設計判断で後述）。

### B. 連続版 mutual information / KL の chain rule（軸 2 中核）

調査結論: **`mutualInfoOfChannel` / `mutualInfo` の連続版 `I = h(Y) − h(Y|X)` 結論形は Mathlib 不在**。だが klDiv の compProd chain rule（density-level 展開の機械）は Mathlib に存在し、これが唯一の足場。

| 概念 | API | file:line | 状態 | bridge での扱い |
|---|---|---|---|---|
| Common2026 MI（KL 形） | `InformationTheory.Shannon.mutualInfo (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞ := klDiv (μ.map (fun ω => (Xs ω, Yo ω))) ((μ.map Xs).prod (μ.map Yo))` | `MutualInfo.lean:37` | ✅ Common2026 自前 | `perLetterMI` の実体。型クラス前提なし（`[MeasurableSpace Ω/X/Y]` のみ、`MutualInfo.lean:31-33`） |
| Common2026 channel MI | `InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel (p : Measure α) (W : Channel α β) : ℝ≥0∞ := klDiv (jointDistribution p W) (p.prod (outputDistribution p W))` | `ChannelCoding.lean:85` | ✅ Common2026 自前 | `IsContChannelMIDecompHyp` 側で使用。`perLetterMI` は `mutualInfo` 形なので直接は別物 |
| **Mathlib KL chain rule** | `InformationTheory.klDiv_compProd_eq_add : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` | `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:204` | ✅ 既存 | **bridge の足場**。第二項 `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` = 条件 KL。型クラス前提（下記ボックス）に注意 |
| **Mathlib KL compProd 左不変** | `InformationTheory.klDiv_compProd_left : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν` | `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:182` | ✅ 既存 | 同 kernel 約分。条件 KL の reshape に使う候補 |
| KL → ∫ llr 展開 | `InformationTheory.toReal_klDiv_of_measure_eq` ほか | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean`（`DifferentialEntropy.lean:543` で使用実績） | ✅ 既存 | `klDiv.toReal = ∫ llr ∂μ` の Real 化（`μ.univ = ν.univ` 前提） |
| rnDeriv chain（測度3段） | `MeasureTheory.Measure.rnDeriv_mul_rnDeriv (h : μ ≪ ν) : μ.rnDeriv ν * ν.rnDeriv volume =ᵐ[volume] μ.rnDeriv volume` | Mathlib（`DifferentialEntropy.lean:548` で使用実績） | ✅ 既存 | density Bayes split の核 |
| ∫ rnDeriv smul 変換 | `MeasureTheory.integral_rnDeriv_smul (hμ : μ ≪ ν) : ∫ g ∂μ = ∫ (μ.rnDeriv ν).toReal • g ∂ν` | Mathlib（`DifferentialEntropy.lean:585` で使用実績） | ✅ 既存 | `∫ … ∂μ` を `∫ … ∂volume` に翻訳して `differentialEntropy` 形に畳む |
| **Mathlib `mutualInfo` (連続)** | — | — | ❌ **Mathlib 不在**（loogle `ProbabilityTheory.mutualInfo` → `unknown identifier`） | 自前 `mutualInfo` を使う |
| **連続 MI = h(Y)−h(Y\|X) 結論形** | — | — | ❌ **Mathlib 不在** | bridge の本体。自作（下記 wall） |

判定（軸 2）: **PARTIAL**。klDiv の compProd chain rule（`klDiv_compProd_eq_add` / `klDiv_compProd_left`）と density 展開の primitive（rnDeriv chain / ∫ llr / integral_rnDeriv_smul）はすべて Mathlib + Common2026 にある。**欠けているのは「これらを束ねて `I = h(Y) − h(Y|X)` の density 等式に到達する補題そのもの」**。

### C. AWGN 特化 — per-letter mixture を chain rule に乗せる橋渡し（軸 3）

| 概念 | API | file:line | 状態 | bridge での扱い |
|---|---|---|---|---|
| per-letter Y law mixture 形 | `perLetterYLaw_eq_mixture` (private) | `AWGNConverseDischarge.lean:563` | ✅ 既存 | `perLetterYLaw = (1/M) ∑ₘ 𝒩(c.encoder m i, N)` |
| per-letter Y law ≪ volume | `perLetterYLaw_absolutelyContinuous` (private) | `AWGNConverseDischarge.lean:624` | ✅ 既存 | density 形に乗せる前提 |
| per-letter Y law 確率測度 | `perLetterYLaw_isProbabilityMeasure` (private) | `AWGNConverseDischarge.lean:612` | ✅ 既存 | `IsProbabilityMeasure` 前提 |
| fibre ≪ volume | `awgnChannel_apply_absolutelyContinuous (N) (hN : N ≠ 0) (h_meas) (x) : (awgnChannel N h_meas) x ≪ volume` | `AWGNMIDecompBody.lean:103` | ✅ 既存 | chain rule の side condition |
| 連続 MI chain predicate（既存 wall） | `IsContChannelMIDecompHyp (p : Measure ℝ) (W : Channel ℝ ℝ) : Prop := (mutualInfoOfChannel p W).toReal = differentialEntropy (outputDistribution p W) - ∫ x, differentialEntropy (W x) ∂p` | `AWGNMIDecompBody.lean:147` | ⚠️ **load-bearing predicate (tier 4)** | **本 task が closure すべき壁の AWGN-非依存版が既にこの形で存在** |
| channel MI = 三項 entropy（**離散のみ**） | `ChannelCoding.mutualInfoOfChannel_eq_HX_add_HY_sub_HZ [Fintype α][DecidableEq α][Nonempty α][MeasurableSingletonClass α][Fintype β]…(p)(W) : (mutualInfoOfChannel p W).toReal = entropy … + entropy … - entropy …` | `ChannelCoding.lean:126` | ✅ 既存だが **離散専用** | **連続 Gaussian には適用不可**（`[Fintype α][Fintype β]` 要求）。discrete analogue として参照のみ |
| **mutualInfoOfChannel ↔ mutualInfo 形変換** | `mutualInfoOfChannel_eq_mutualInfo_prod (p)[IsProbabilityMeasure p](W)[IsMarkovKernel W] : mutualInfoOfChannel p W = mutualInfo (jointDistribution p W) Prod.fst Prod.snd` | `ChannelCoding.lean:96` | ✅ 既存 | `perLetterMI`(=`mutualInfo` 形) と `mutualInfoOfChannel` 形の往復に使える可能性 |
| **`awgnConverseJoint` の compProd 因子分解** | — | — | ❌ **未提供**（`AWGNConverseDischarge.lean:150` に「condDistrib joint factorization 導出が bridge 上限超で断念」と明記） | `klDiv_compProd_eq_add` を当てるには `(awgnConverseJoint).map (X_i,Y_i) = p_i ⊗ₘ κ` が必要。**最大 plumbing リスク** |

判定（軸 3）: **PARTIAL**。AWGN fibre の正則性・mixture closed form・fibre entropy 不変はすべて既存。だが `perLetterMI` を Mathlib `klDiv_compProd_eq_add` に乗せるための「joint = input ⊗ₘ AWGN kernel」因子分解が無い。これは過去 session で Route A として試みて bridge 上限を超えて断念された（`AWGNConverseDischarge.lean:149-151`）。

### D. condEntropy / disintegration（軸 2 補助）

| 概念 | API | file:line | 状態 | bridge での扱い |
|---|---|---|---|---|
| Mathlib `condEntropy`（連続/測度版） | — | — | ❌ **Mathlib 不在**（loogle `ProbabilityTheory.condEntropy` → `unknown identifier`） | 自前 `∫ x, differentialEntropy (W x) ∂p` で条件 entropy を表現（`IsContChannelMIDecompHyp` の右第二項がまさにこの形） |
| Common2026 離散 `mutualInfo_eq_entropy_sub_condEntropy` | `InformationTheory.Shannon.mutualInfo_eq_entropy_sub_condEntropy` | `Bridge.lean:588` | ✅ 既存だが**離散専用** | discrete analogue。連続版の参照点のみ |
| `condDistrib` + `klDiv` 連携 | — | — | ❌ **Mathlib 不在**（loogle `ProbabilityTheory.condDistrib, InformationTheory.klDiv` → `Found 0 declarations`） | Mathlib に「条件分布で書いた KL」は無い。compProd 形で迂回するしかない |

判定（軸 2 補助）: **NEGATIVE**。Mathlib は条件エントロピー / 条件 MI を連続測度上で提供しない。条件 entropy は本プロジェクト流儀（fibre 微分エントロピーの積分 `∫ h(W x) dp`）で表すしかなく、これは既に `IsContChannelMIDecompHyp` 右第二項として確立済。

---

## 主要前提条件ボックス（事故が起きやすい lemma）

**`InformationTheory.klDiv_compProd_eq_add`（`ChainRule.lean:204`）の型クラス前提（verbatim、`ChainRule.lean:88-90`）:**

- `{𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}`
- `{μ ν : Measure 𝓧} {κ η : Kernel 𝓧 𝓨}`
- `[IsFiniteMeasure μ] [IsFiniteMeasure ν]`
- `[IsMarkovKernel κ] [IsMarkovKernel η]`
- 結論 verbatim: `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`
- **`[StandardBorelSpace _]` は不要**（docstring 明記「holds without any assumption on the measurable spaces」）。これは positive surprise — Fano Phase 3 の `condDistrib` が StandardBorel を要求したのと対照的。
- ただし「左の compProd 形 `μ ⊗ₘ κ`」を組むこと自体が要件。`perLetterMI` の joint は `(awgnConverseJoint).map (X_i, Y_i)` であり、これを `p_i ⊗ₘ κ_i`（`κ_i` = AWGN kernel `Kernel ℝ ℝ`）に**書き換える補題が前提として要る**（軸 C の未提供項）。`q_i`（出力 marginal）側は `ν := p_i`, `η := const q_i` 形に乗せる必要があり、ここで `η` を `IsMarkovKernel` にするには `q_i` を定数 kernel `Kernel.const ℝ q_i` で包む。

**`klDiv` → `∫ llr` Real 化（`toReal_klDiv_of_measure_eq`、`DifferentialEntropy.lean:543` 使用実績）の前提:**

- `μ ≪ ν`（絶対連続）
- `μ Set.univ = ν Set.univ`（全質量一致、確率測度なら自明）
- toReal が finite であること（`klDiv ≠ ∞`）を別途要する。`perLetterMI ≠ ∞` は `awgnConverseJoint_pair_mi_ne_top` が `wall:multivariate-mi` として `AWGNConverseDischarge.lean` に別途残置（本 bridge とは別 wall）。

**`differentialEntropy_eq_integral_density`（`DifferentialEntropy.lean:65`）の前提:**

- `f` measurable かつ `0 ≤ f`（density）
- `μ = volume.withDensity (ENNReal.ofReal ∘ f)`（density 形で μ を表現済であること）
- density 展開した chain rule の各項を `differentialEntropy` 結論形に畳む最終ステップで、各 measure の density 表現が要る。mixture-of-Gaussians の density は `perLetterYLaw_eq_mixture` から組めるが plumbing 量がある。

---

## 自作が必要な要素（優先度順）

1. **連続版 MI chain rule 補題（最重要・唯一の真の壁）**
   - 結論形: 抽象 `mutualInfo`（or `mutualInfoOfChannel`）の連続版 `I(X;Y) = h(Y) − ∫ h(W x) dp`。既存の `IsContChannelMIDecompHyp`（`AWGNMIDecompBody.lean:147`）がまさにこの結論形を **predicate として** 持っている。
   - 推奨実装: `klDiv_compProd_eq_add` で `I = klDiv p_i p_i + klDiv (p⊗ₘκ)(p⊗ₘη)`（左項 = 0、第二項 = 条件 KL）に分解 → `toReal_klDiv_of_measure_eq` で `∫ llr` 化 → `rnDeriv_mul_rnDeriv` で density Bayes split → `integral_rnDeriv_smul` で `∂μ → ∂volume` 翻訳 → `differentialEntropy_eq_integral_density` で両 entropy 項に畳む。
   - 工数感: 自前 docstring 推定 **200-300 行**（`AWGNMIDecompBody.lean:43-45` の見積もり、および `klDiv_gaussianReal_gaussianReal_eq`（`DifferentialEntropy.lean:672`、~210 行の類似 density 計算）を参照点とする）。Fubini / integrability bookkeeping が支配的。
   - 落とし穴: (a) `η`（出力周辺を定数 kernel 化）を `IsMarkovKernel` にする型合わせ、(b) llr の可積分性（`integrable_llr_compProd_iff`、`ChainRule.lean:156`）を per-letter mixture で示す、(c) 条件 entropy 項の符号（`-∫ h` で `negMulLog` の符号反転を取り違えやすい）。

2. **per-letter mixture を `compProd` 形に乗せる橋渡し（plumbing、軸 C）**
   - 結論形: `(awgnConverseJoint h_meas c).map (fun ω => (c.encoder ω.1 i, ω.2 i)) = p_i ⊗ₘ (Kernel.const _ ∘ awgnChannel …)` 相当の因子分解。または `perLetterMI = mutualInfoOfChannel p_i κ_i` への往復（`mutualInfoOfChannel_eq_mutualInfo_prod`（`ChannelCoding.lean:96`）の逆向き利用）。
   - 工数感: **30-80 行**。`awgnConverseJoint` が mixture（`(1/M) ∑ₘ dirac m ⊗ pi`）なので、第 i 座標への射影 + 入力 marginal `p_i = (1/M) ∑ₘ dirac (c.encoder m i)` の取り出しが必要。
   - 落とし穴: 過去 session が Route A（`condDistrib` factorization）で同種の因子分解を試みて bridge 上限超で断念（`AWGNConverseDischarge.lean:149-151`）。**ここが軸 3 最大の plumbing リスク**。mixture を直接 compProd に乗せず、線形性で各 m 成分に分けてから合算する経路を推奨。

3. **`h(𝒩(x,N)) = h(𝒩(0,N))` 条件 entropy 平均不変（既に genuine 済、再利用）**
   - `differentialEntropy_awgnChannel_apply_eq_noise`（`AWGNMIBridge.lean:108`）。`∫ h(awgnChannel x) dp = ∫ h(𝒩(0,N)) dp = h(𝒩(0,N))`（定数の積分）。新規実装ほぼ不要。

---

## Mathlib 壁の列挙

真に Mathlib 不在で `@residual(wall:…)` 対象になりうるもの:

1. **連続版 MI chain rule `I(X;Y) = h(Y) − h(Y|X)`（density-level）** — `wall:awgn-mi-decomp`（既存 slug、`AWGNMIDecompBody.lean` Mathlib gap セクション参照）。
   - loogle 確認: `ProbabilityTheory.mutualInfo` → `unknown identifier`、`differentialEntropy` → `unknown identifier`、`ProbabilityTheory.condDistrib, InformationTheory.klDiv` → **`Found 0 declarations`**。
   - **shared sorry 補題化 強く推奨**: この壁は本 task 専用ではない。既に `IsContChannelMIDecompHyp`（`AWGNMIDecompBody.lean:147`、AWGN 非依存・generic channel 形）として load-bearing predicate（tier 4 寄り）の形で存在し、`AWGNMIBridge.lean` の `IsAwgnMIDecomp`（`AWGNMIBridge.lean:135`）経由で `mutualInfoOfChannel_gaussianInput_closed_form`（`AWGN.lean:125`）の `h_bridge` 引数にも繋がる。**同一の density chain rule 壁が ① 本 task の per-letter（`mutualInfo` 形）、② `IsContChannelMIDecompHyp`（`mutualInfoOfChannel` 形・generic 入力）、③ `IsAwgnMIDecomp`（AWGN 単一 Gaussian 入力）の 3 箇所に散在**。`docs/audit/audit-tags.md`「共有 Mathlib 壁: shared sorry 補題パターン」に従い、AWGN 非依存の generic channel 版 1 本（例: `contChannelMIDecomp_holds (p) (W) [IsMarkovKernel W] [...] : (mutualInfoOfChannel p W).toReal = differentialEntropy (outputDistribution p W) - ∫ x, differentialEntropy (W x) ∂p := by sorry`、`@residual(wall:awgn-mi-decomp)`）に集約し、per-letter / AWGN-Gaussian 各形はその shared 補題 + plumbing で導く構成を推奨。

2. （壁ではないが要注意）**`perLetterMI ≠ ∞`** — `wall:multivariate-mi`（`AWGNConverseDischarge.lean` の `awgnConverseJoint_pair_mi_ne_top`、本 bridge とは別 wall として既に残置）。bridge を `toReal` 等式として書く以上、finiteness は別途必要だが本 task のスコープ外。

---

## 撤退ラインへの距離

親 plan `awgn-mi-bridge-plan.md` の撤退ライン（Closure criteria, `awgn-mi-bridge-plan.md:42-45`）:

> - `h_bridge` 引数を `mutualInfoOfChannel_gaussianInput_closed_form` から削除（genuine discharge）、または別の `IsAwgnGaussianMIBridge` staged predicate に振り替え。

判定: **発動しない**（本 inventory は壁を「Mathlib 不在の density chain rule」と確定しただけで、撤退ライン抵触なし）。ただし本 task の現状（`AWGNConverse.lean` の `h_mi_bridge_per_letter` sorry）は **既に `predicate` 形ではなく `sorry + @residual` 形に migrate 済**（tier 2、honest）であり、撤退ラインの「staged predicate に振り替え」は**むしろ後退**になる点に注意。

新規撤退ラインの提案（縮退案、撤退口は sorry + `@residual`）:

- **連続 MI chain rule shared 補題（自作要素 1）が 200-300 行で書けない場合**
  → 壁を `wall:awgn-mi-decomp` の shared sorry 補題 1 本に集約したまま残置（per-letter / generic / AWGN-Gaussian の 3 形を全部その 1 補題に delegate）。`AWGNConverse.lean` の per-letter sorry は shared 補題呼び出し + plumbing に置換して honest sorry を 1 箇所に縮約。
- **mixture → compProd 因子分解（自作要素 2）が plumbing 上限を超える場合**（過去 Route A 断念の再来）
  → per-letter を経由せず、`mutualInfoOfChannel` 形（generic 入力 `p_i`）で chain rule を当て、`perLetterMI = mutualInfoOfChannel p_i κ_i` の往復補題（`mutualInfoOfChannel_eq_mutualInfo_prod` 逆向き）を別 sorry（`@residual(plan:awgn-mi-bridge-plan)`）で繋ぐ縮退。仮説束化は禁止。

いずれも仮説束化せず sorry + `@residual` で抜く。

---

## 着手 skeleton

> 本 task は **既存 file 拡張**（新規 file 推奨ではない）。shared 壁補題は AWGN 非依存なので `AWGNMIDecompBody.lean`（既に `IsContChannelMIDecompHyp` が住む）または専用 `AwgnWalls.lean`（converse 壁の集約先、`AWGNConverseDischarge.lean:138` 参照）への追加が筋。以下は shared 壁補題 + per-letter 橋渡しの skeleton。

```lean
import Common2026.Meta.EntryPoint
import Common2026.Shannon.AWGNMIBridge          -- IsContChannelMIDecompHyp / differentialEntropy_awgnChannel_apply_eq_noise
import Mathlib.InformationTheory.KullbackLeibler.ChainRule  -- klDiv_compProd_eq_add / klDiv_compProd_left

namespace InformationTheory.Shannon.AWGN

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

/-- **Shared Mathlib wall: continuous-channel MI chain rule** (AWGN 非依存).
`I(X;Y) = h(Y) − ∫ h(W x) dp`. Mathlib 不在 (klDiv_compProd_eq_add を density-level
に展開する 200-300 行が要、連続版 mutualInfo / condEntropy / differentialEntropy は
いずれも Mathlib 未掲載)。per-letter / AWGN-Gaussian 各 bridge はこの 1 本に集約。
@residual(wall:awgn-mi-decomp) -/
theorem contChannelMIDecomp_holds
    (p : Measure ℝ) [IsProbabilityMeasure p]
    (W : InformationTheory.Shannon.ChannelCoding.Channel ℝ ℝ) [IsMarkovKernel W] :
    (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel p W).toReal
      = Common2026.Shannon.differentialEntropy
          (InformationTheory.Shannon.ChannelCoding.outputDistribution p W)
        - (∫ x, Common2026.Shannon.differentialEntropy (W x) ∂p) := by
  sorry  -- @residual(wall:awgn-mi-decomp)

/-- per-letter bridge: shared 壁補題 + mixture→compProd 橋渡し + fibre entropy 不変
で `(perLetterMI).toReal = h(perLetterYLaw) − h(𝒩(0,N))` に到達。橋渡しが詰まれば
sorry + @residual(plan:awgn-mi-bridge-plan) で抜く。 -/
theorem awgn_per_letter_mi_bridge
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    (perLetterMI h_meas c i).toReal
      = Common2026.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
        - Common2026.Shannon.differentialEntropy (gaussianReal 0 N) := by
  sorry  -- @residual(plan:awgn-mi-bridge-plan)

end InformationTheory.Shannon.AWGN
```

着手順: ① `contChannelMIDecomp_holds` を `klDiv_compProd_eq_add` 足場で density 展開（自作要素 1）。② `awgn_per_letter_mi_bridge` を mixture→compProd 橋渡し（自作要素 2）+ ① 呼び出し + `differentialEntropy_awgnChannel_apply_eq_noise`（自作要素 3、既存）で構成。③ `AWGNConverse.lean:86` の honest residual を `awgn_per_letter_mi_bridge` 呼び出しに置換。
