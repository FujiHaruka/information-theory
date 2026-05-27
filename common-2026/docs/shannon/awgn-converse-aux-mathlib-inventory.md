# AWGN F-3 converse-aux — Mathlib + Common2026 在庫

> 親 plan: [`awgn-converse-aux-plan.md`](awgn-converse-aux-plan.md) (1043 行、`8ee2eea`)
>
> 親 plan §Phase 0 (line 372-424) で要求された 5 判断 (#1-#5) を裏取りする。
> 出力先は `docs/shannon/`、Lean code は touch しない。

## 一行サマリ

**Phase 0 判定 — Mathlib + Common2026 在庫率 ~75% / 自作必要 ~3 件 / T-FFC-2 と T-FFC-3 確定発動見込み**。
**最大発見 (危険度: 中)**: 既存 `shannon_converse_single_shot`
(`Common2026/Shannon/Converse.lean:81`) が Fano + DPI + uniform-W + entropy chain
を **1 補題に既に集約済み** で AWGN converse の **(a)+(b)+(d) 全 step を内包**。
Y 側に `Fintype` 制約なし (Y := `Fin n → ℝ` で起動可) ⇒ 本 plan の Phase B-Fano
+ B-DPI 大部分は既存 1 補題呼出に圧縮可能。残るは **(c) memoryless chain rule の
Mathlib 壁 (Fintype α 制約付き既存補題は AWGN α := ℝ で reuse 不可)** + **per-letter
Gaussian max-entropy** の 2 件、これが本 plan の核。判断 #2 で「entropy chain
rule + uniform W 在庫」は **完全在庫 (genuine 化可)**、判断 #3 (DPI continuous)
も genuine 化可、判断 #4 (continuous MI chain rule) のみ確定 staged。**規模予測
の中央値は plan 中央 650 行から ~450-550 行に下方修正可能**。

---

## 主定理の最終形 (再掲、parent plan より)

```lean
theorem isAwgnConverseFeasible_discharger
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_feasible : IsAwgnConverseFeasible P N h_meas)
    {M n : ℕ} (hM : 2 ≤ M) (c : AwgnCode M n P)
    (Pe : ℝ)
    (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by …
```

証明戦略 (pseudo-Lean、適用予定の補題を併記):

```lean
-- (1) shannon_converse_single_shot で log M ≤ I(W; Y^n).toReal + binEntropy + Pe·log
--     (W uniform on Fin M、Y := Fin n → ℝ、decoder : Y^n → Fin M)
--     ⇒ Fano + DPI + entropy chain + log M = H(W uniform) を 1 補題で吸収
have h_single := shannon_converse_single_shot μ W Y^n c.decoder
    hW hY^n c.decoder_meas h_uniform hM h_mi_finite
-- (2) bundle.chain で I(W; Y^n) ≤ ∑ I(X_i; Y_i)
--     (現状は: I(W; Y^n) ≤ I(X^n; Y^n) ≤ ∑ I(X_i; Y_i) の 2 段、または直接束)
have h_chain := h_feasible.chain ...
-- (3) bundle.per_letter で各 i: I(X_i; Y_i) ≤ (1/2) log(1+P/N)
--     (Gaussian Y_i max-entropy + per-letter integrability)
have h_per := h_feasible.per_letter ...
-- (4) 算術: ∑ (1/2) log(1+P/N) = n · (1/2) log(1+P/N)
linarith [Finset.sum_const, …]
```

---

## API 在庫テーブル

### A. Fano (Common2026 既存、genuine 化可)

| 概念 | API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| **Fano measure form** | `theorem fano_inequality_measure_theoretic (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (decoder : Y → X) (hXs : Measurable Xs) (hYo : Measurable Yo) (hdec : Measurable decoder) (hcard : 2 ≤ Fintype.card X) : condEntropy μ Xs Yo ≤ Real.binEntropy (errorProb μ Xs Yo decoder) + errorProb μ Xs Yo decoder * Real.log ((Fintype.card X : ℝ) - 1)` | `Common2026/Fano/Measure.lean:226` | 🟢 | Y 側に型制約なし (`X` 側だけ `[Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X] [MeasurableSingletonClass X]` を section variable で要求)。本 plan で `X := Fin M, Y := Fin n → ℝ` で起動。Y のクラス要件は無いので `[StandardBorelSpace (Fin n → ℝ)]` 等の type-class 自動推論失敗 (T-FFC-1) は **発生しない見込み**。 |
| **Fano `condEntropy` 定義** (Y 上 ∫) | `def condEntropy (μ : Measure Ω) [IsFiniteMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) : ℝ := ∫ y, ∑ x : X, Real.negMulLog ((condDistrib Xs Yo μ y).real {x}) ∂(μ.map Yo)` | `Common2026/Fano/Measure.lean:69` | 🟢 | Y 側無制約、`X` 側のみ `[Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]` (section variable)。AWGN で `Y := Fin n → ℝ` は無条件 OK。 |
| **Fano `errorProb` (Real)** | `def errorProb (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) (decoder : Y → X) : ℝ := μ.real {ω | Xs ω ≠ decoder (Yo ω)}` | `Common2026/Fano/Measure.lean:74` | 🟢 | `μ.real` 形 (Real)、本 plan 結論の `Pe : ℝ` と同型。 |

**Section type-class** (`Common2026/Fano/Measure.lean:55-61` 周辺):

```
variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  [MeasurableSpace X] [MeasurableSingletonClass X]
variable {Y : Type*} [MeasurableSpace Y]
```

→ `X := Fin M` (`M ≥ 2`) は `Fin.fintype` + `Fin.decidableEq` + `Fin.instMeasurableSpace` + `Fin.instMeasurableSingletonClass` ですべて自動 (Nonempty は `M ≥ 2` → `Fin M` Nonempty)。`Y := Fin n → ℝ` は `[MeasurableSpace (Fin n → ℝ)]` 自動 (`Pi.measurableSpace`)。**T-FFC-1 は発動しない**。

### B. Single-shot Converse (Common2026 既存、**本 plan 最大発見**)

| 概念 | API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| **★ Shannon single-shot converse** | `theorem shannon_converse_single_shot (μ : Measure Ω) [IsProbabilityMeasure μ] (Msg : Ω → M) (Yo : Ω → Y) (decoder : Y → M) (hMsg : Measurable Msg) (hYo : Measurable Yo) (hdecoder : Measurable decoder) (hMsg_uniform : μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count) (hcard : 2 ≤ Fintype.card M) (hMI_finite : mutualInfo μ Msg Yo ≠ ∞) : Real.log (Fintype.card M) ≤ (mutualInfo μ Msg Yo).toReal + Real.binEntropy (InformationTheory.MeasureFano.errorProb μ Msg Yo decoder) + InformationTheory.MeasureFano.errorProb μ Msg Yo decoder * Real.log ((Fintype.card M : ℝ) - 1)` | `Common2026/Shannon/Converse.lean:81` | 🟢 **核心** | **Fano + DPI + entropy chain + `H(W uniform) = log M` を 1 補題に集約**。本 plan の **Phase B-Fano + B-DPI を 1 行に圧縮**。**Y 側は無制約 `[MeasurableSpace Y]` のみ** ⇒ `Y := Fin n → ℝ` で直接起動可 (T-FFC-1 完全回避)。 |
| **uniform W entropy = log M (helper)** | `private lemma entropy_of_uniform_msg (μ : Measure Ω) (Msg : Ω → M) (hMsg_uniform : μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count) : entropy μ Msg = Real.log (Fintype.card M)` | `Common2026/Shannon/Converse.lean:56` | 🟢 (private、`shannon_converse_single_shot` 内で吸収済) | 別途呼ばずに `shannon_converse_single_shot` 経由で消費。 |

**Section type-class** (`Common2026/Shannon/Converse.lean:48-51`):

```
variable {Ω : Type*} [MeasurableSpace Ω]
variable {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
  [MeasurableSpace M] [MeasurableSingletonClass M]
variable {Y : Type*} [MeasurableSpace Y]
```

→ `M := Fin M_count` で全自動充足、`Y := Fin n → ℝ` 無条件 OK。

**注意 (重要)**: `shannon_converse_single_shot` の引数 `decoder : Y → M` は **measurable** (`hdecoder`) が必要、AWGN `c.decoder_meas` (`AWGN.lean:101`) で discharge 可。`hMI_finite : mutualInfo μ Msg Yo ≠ ∞` も必要 — `Msg = W : Ω → Fin M` (有限) + Y 無限の場合の MI finite 化は **separate 補題**で要確認 (本 plan Phase B-Fano 内の plumbing として ~10-20 行)。

### C. Memoryless MI chain rule (Common2026 既存、**`Fintype α` 制約あり → AWGN α := ℝ で reuse 不可、staged 確定**)

| 概念 | API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| **MI chain rule (memoryless, n-letter)** | `theorem mutualInfo_le_sum_per_letter_of_memoryless_strong (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β) (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i)) (h_per_letter_markov : ∀ i : Fin n, IsMarkovChain μ (fun ω j => Xs j ω) (Xs i) (Ys i)) (h_outputs_cond_indep : ∀ i : Fin n, IsMarkovChain μ (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω) (fun ω j => Xs j ω) (Ys i)) : (mutualInfo μ (fun ω j => Xs j ω) (fun ω j => Ys j ω)).toReal ≤ ∑ i : Fin n, (mutualInfo μ (Xs i) (Ys i)).toReal` | `Common2026/Shannon/CondEntropyMemoryless.lean:552` | 🔴 **AWGN α := ℝ で reuse 不可** | **Section variable に `[Fintype α] [Fintype β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]` 等の有限性制約あり** (Bridge.lean entropy 定義の連鎖)。AWGN α := β := ℝ では発火しない ⇒ **T-FFC-3 staged 確定発動**。bundle `ContinuousMIChainRuleForConverse` に集約。 |
| **MI chain rule (general n-letter, KL form)** | `theorem mutualInfo_chain_rule_fin {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] [StandardBorelSpace Y] [Nonempty Y] (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (Yo : Ω → Y) (hYo : Measurable Yo) : mutualInfo μ (fun ω i => Xs i ω) Yo = ∑ i : Fin n, condMutualInfo μ (Xs i) Yo (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)` | `Common2026/Shannon/MIChainRule.lean:93` | 🟡 部分利用可 | Section variable: `{α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α]` ⇒ **α := ℝ で発火しない**。`Y := Fin n → ℝ` ⇒ `[StandardBorelSpace (Fin n → ℝ)]` は Mathlib `instStandardBorelSpacePi` で自動充足見込み。AWGN converse での α := ℝ block は不可。 |
| **MI additivity under product joint (iid → sum)** | `theorem mutualInfo_pi_eq_sum {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β) (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i)) (h_iid_joint : …) (h_iid_X : …) (h_iid_Y : …) : mutualInfo μ (fun ω i => Xs i ω) (fun ω i => Ys i ω) = ∑ i : Fin n, mutualInfo μ (Xs i) (Ys i)` | `Common2026/Shannon/MIChainRule.lean:318` | 🟡 部分利用可 | Section variable `{α β : Type*} [MeasurableSpace α] [MeasurableSpace β]` **無 Fintype** ⇒ **α := β := ℝ で発火可**。**ただし** `μ.map (fun ω i => (X_i ω, Y_i ω)) = Measure.pi (μ.map (X_i, Y_i))` の **iid joint 仮定** が必要 — AWGN converse は **コード由来の X^n は iid でない** (codebook 各 message ごとに固定の deterministic 行) ⇒ 直接 iid 仮定で起動不可。Markov chain 補題 (`mutualInfo_le_of_markov`) + chain rule + 加法性の組み合わせで bound に持っていく必要があり、これが Mathlib 壁の核。 |
| **AWGN-agnostic continuous chain rule (predicate)** | `def IsContChannelMIDecompHyp (p : Measure ℝ) (W : Channel ℝ ℝ) : Prop := (mutualInfoOfChannel p W).toReal = differentialEntropy (outputDistribution p W) - (∫ x, differentialEntropy (W x) ∂p)` | `Common2026/Shannon/AWGNMIDecompBody.lean:147` | 🟡 (姉妹 `awgn-mi-decomp-plan.md` Phase 6 が discharge 予定) | これは **1 文字 chain rule** (`I(X;Y) = h(Y) - h(Y|X)`)、n 文字 chain rule の memoryless 加法性 (`I(X^n;Y^n) ≤ ∑ I(X_i;Y_i)`) ではない。本 plan の T-FFC-3 staged hyp と相補だが直接置換不可。 |

**判定**: AWGN α := β := ℝ で **continuous MI memoryless chain rule** `I(X^n;Y^n) ≤ ∑ I(X_i;Y_i)` を **AWGN code (non-iid codebook) で genuine 化する** 補題は **Mathlib + Common2026 不在**。**T-FFC-3 staged 確定発動**。

### D. DPI (data processing inequality)

| 概念 | API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| **DPI postprocess** | `theorem mutualInfo_le_of_postprocess (μ : Measure Ω) [IsFiniteMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo) {f : Y → Z} (hf : Measurable f) : mutualInfo μ Xs (f ∘ Yo) ≤ mutualInfo μ Xs Yo` | `Common2026/Shannon/DPI.lean:142` | 🟢 | Section variable: `{Ω : Type*} [MeasurableSpace Ω] {X : Type*} [MeasurableSpace X] {Y : Type*} [MeasurableSpace Y] {Z : Type*} [MeasurableSpace Z]` ⇒ **無 Fintype、AWGN で直接 reuse 可**。`shannon_converse_single_shot` 内部で消費済。 |
| **DPI via Markov chain** | `theorem mutualInfo_le_of_markov (μ : Measure Ω) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo) (hmarkov : IsMarkovChain μ Xs Zc Yo) : mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo` | `Common2026/Shannon/CondMutualInfo.lean:385` | 🟢 | `X := Fin M`, `Y := Fin n → ℝ`, `Z := Fin n → ℝ` で起動可。X 側 StandardBorel は `Fin M` (`Finite.standardBorelSpace`)、Y 側 `Fin n → ℝ` (`instStandardBorelSpacePi`) 自動充足見込み。**Markov chain 仮定** `IsMarkovChain μ W X^n Y^n` は AWGN 通信路の自然な帰結 (encoder deterministic + channel memoryless)、bundle 内 staged にするか genuine 化するかは Phase 0 判定 #3。**判定: 在庫あり、genuine 化候補**。 |

**DPI continuous 判定 (判断 #3)**: Common2026 既存補題で十分。`shannon_converse_single_shot` が DPI を吸収済み + 別途 `mutualInfo_le_of_markov` で Markov chain `W → X^n → Y^n` の DPI も処理可。**T-FFC-3 の DPI 側は staged 不要、本 plan で genuine 化可**。

### E. Per-letter Gaussian max-entropy (Common2026 既存、3-of-4 hyp genuine、`h_ent_int` のみ Mathlib 壁)

| 概念 | API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| **Gaussian max-entropy 4-hyp 形** | `theorem differentialEntropy_le_gaussian_of_variance_le {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : μ ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (h_mean : ∫ x, x ∂μ = m) (h_var : ∫ x, (x - m)^2 ∂μ ≤ (v : ℝ)) (h_var_int : Integrable (fun x => (x - m)^2) μ) (h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) : differentialEntropy μ ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)` | `Common2026/Shannon/DifferentialEntropy.lean:518` | 🟢 (3-of-4 genuine、`h_ent_int` のみ wall) | per-letter `μ := μ_{Y_i}` で起動。`hμ` は Gaussian convolution で genuine、`h_mean` `h_var` は AWGN code 由来 (power constraint)、`h_var_int` は Gaussian-mixture moment で genuine、**`h_ent_int` のみ Mathlib 壁** → **T-FFC-2 staged 確定発動** (bundle `PerLetterIntegrabilityForConverse`)。 |
| **Gaussian closed form** | `theorem differentialEntropy_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : differentialEntropy (gaussianReal m v) = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)` | `Common2026/Shannon/DifferentialEntropy.lean:412` | 🟢 | `h(Z) = (1/2) log(2πeN)` を取るのに使用 (per-letter `h(Y_i\|X_i) = h(Z_i)`)。 |
| **AWGN fibre ≪ volume** | `theorem awgnChannel_apply_absolutelyContinuous (N : ℝ≥0) (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N) (x : ℝ) : (awgnChannel N h_meas) x ≪ volume` | `Common2026/Shannon/AWGNMIDecompBody.lean:103` | 🟢 | per-letter `Y_i\|X_i` density 表現に使う。 |
| **Mathlib: `gaussianReal_conv_gaussianReal`** | `lemma gaussianReal_conv_gaussianReal {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} : (gaussianReal m₁ v₁) ∗ (gaussianReal m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ + v₂)` | `.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/Real.lean:613` | 🟢 | `μ_{Y_i} = μ_{X_i} ∗ N(0, N)` convolution 計算 (X_i は任意分布で OK、Y_i は X_i ∗ N(0,N) ⇒ Gaussian mixture)。**注**: `μ_{X_i}` は AWGN code 由来で **Gaussian と限らない** ⇒ 直接 `gaussianReal_conv_gaussianReal` 適用不可。`μ_{Y_i} = ∫ gaussianReal x N ∂μ_{X_i}(x)` の mixture density で扱う必要あり (T-FFC-2 staged で吸収するのが妥当)。 |
| **Mathlib: `gaussianReal_add_gaussianReal_of_indepFun`** | `lemma gaussianReal_add_gaussianReal_of_indepFun {Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} {X Y : Ω → ℝ} (hXY : IndepFun X Y P) (hX : P.map X = gaussianReal m₁ v₁) (hY : P.map Y = gaussianReal m₂ v₂) : P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂)` | `.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/Real.lean:624` | 🟢 | 同上、typed RV 形。X_i 側は generic ⇒ direct reuse 不可、staged で。 |
| **Mathlib: `variance_id_gaussianReal`** | `lemma variance_id_gaussianReal : Var[id; gaussianReal μ v] = v` | `.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/Real.lean:543` | 🟢 | per-letter Z_i variance = N の確認。 |
| **Mathlib: `integral_id_gaussianReal`** | `lemma integral_id_gaussianReal : ∫ x, x ∂gaussianReal μ v = μ` | `.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/Real.lean:508` | 🟢 | per-letter Z_i mean = 0 の確認。 |
| **Mathlib: `integral_rnDeriv_smul`** | `MeasureTheory.integral_rnDeriv_smul (from Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym)` | (Mathlib) | 🟢 | `∫ log (μ.rnDeriv vol).toReal ∂μ = -h(μ)` の証明に既に使用 (`DifferentialEntropy.lean:583`)。 |

### F. AWGN code / channel (Common2026 既存)

| 概念 | API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| **AWGN code** | `structure AwgnCode (M n : ℕ) (P : ℝ) where encoder : Fin M → (Fin n → ℝ); decoder : (Fin n → ℝ) → Fin M; decoder_meas : Measurable decoder; power_constraint : ∀ m : Fin M, (∑ i : Fin n, (encoder m i)^2) ≤ (n : ℝ) * P` | `Common2026/Shannon/AWGN.lean:98` | 🟢 | encoder deterministic、decoder measurable (T-FFC-1 plumbing 不要)、power constraint `∑ (X_i)² ≤ nP` 形 → per-letter `E[X_i²] ≤ P` (uniform W 上平均) で B-Gauss-1 に直結。 |
| **AWGN channel kernel** | `noncomputable def awgnChannel (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : Channel ℝ ℝ where toFun x := gaussianReal x N; measurable' := h_meas` + `instance awgnChannel.instIsMarkovKernel` (`AWGN.lean:83`) | `Common2026/Shannon/AWGN.lean:74-87` | 🟢 | `IsMarkovKernel` instance 自動、本 plan で頻用。 |
| **AWGN measurability hyp** | `def IsAwgnChannelMeasurable (N : ℝ≥0) : Prop := Measurable (fun x : ℝ => gaussianReal x N)` | `Common2026/Shannon/AWGN.lean:64` | 🟢 (F-4 hypothesis 形、`awgn-f1-discharge-moonshot-plan.md` で discharge 済) | 本 plan は hypothesis として受け取り pass-through。 |
| **AWGN code errorProbAt** | `noncomputable def errorProbAt (c : Code M n α β) (W : Channel α β) (m : Fin M) : ℝ≥0∞ := (Measure.pi (fun i => W (c.encoder m i))) (c.errorEvent m)` | `Common2026/Shannon/ChannelCoding.lean:195` | 🟢 (`ℝ≥0∞` 値) | **注意**: AWGN 結論の `Pe : ℝ` は `(c.toCode.errorProbAt ... m).toReal` の sum、Fano `errorProb : ℝ` は `μ.real {Xs ≠ decoder ∘ Yo}` 形。同値性 bridge は **uniform W on `Fin M` + product channel `Measure.pi (awgnChannel ...)`** から導出 (本 plan Phase B-Fano 内で ~20-40 行)。`shannon_converse_single_shot` が **Fano `errorProb` 形を返す** ⇒ AWGN `Pe` との bridge を Phase B-Fano 内で挟む必要あり。 |
| **Code errorEvent** | `def errorEvent (c : Code M n α β) (m : Fin M) : Set (Fin n → β) := (c.decodingRegion m)ᶜ` | `Common2026/Shannon/ChannelCoding.lean:173` | 🟢 | `c.encoder m i` を入力した時の channel output の誤り集合。`errorProbAt` で使用。 |
| **Code Channel definition** | `abbrev Channel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] := Kernel α β` | `Common2026/Shannon/ChannelCoding.lean:50` | 🟢 | `awgnChannel : Channel ℝ ℝ = Kernel ℝ ℝ`、本 plan で `Measure.pi (fun i => awgnChannel N h_meas (encoder m i))` 形を扱う。 |
| **`outputDistribution`** | `noncomputable def outputDistribution (p : Measure α) (W : Channel α β) : Measure β := (jointDistribution p W).snd` | `Common2026/Shannon/ChannelCoding.lean:72` | 🟢 | per-letter `μ_{Y_i}` の表現に使う可能性 (in bundle `PerLetterIntegrabilityForConverse`)。 |
| **`mutualInfoOfChannel`** | `noncomputable def mutualInfoOfChannel (p : Measure α) (W : Channel α β) : ℝ≥0∞ := klDiv (jointDistribution p W) (p.prod (outputDistribution p W))` | `Common2026/Shannon/ChannelCoding.lean:85` | 🟢 | 本 plan の per-letter `I(X_i; Y_i)` を `mutualInfoOfChannel` 形で扱うか、`mutualInfo μ X_i Y_i` (typed RV 形) で扱うかは Phase A 判断。後者の方が `shannon_converse_single_shot` 出力と整合。 |

### G. Markov chain + condDistrib (Common2026 既存)

| 概念 | API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| **`IsMarkovChain` (γ-form)** | `def IsMarkovChain (μ : Measure Ω) [IsFiniteMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) : Prop := μ.map (fun ω => (Zc ω, Xs ω, Yo ω)) = (μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ))` | `Common2026/Shannon/CondMutualInfo.lean:73` | 🟢 | AWGN Markov chain `W → X^n → Y^n` を構築するのに使う。`[StandardBorelSpace X] [StandardBorelSpace Y]` が **X 側 = `Fin M`** (Finite) + **Y 側 = `Fin n → ℝ`** で自動充足見込み。 |
| **mutualInfo chain rule (`I((Z,X);Y) = I(Z;Y) + I(X;Y\|Z)`)** | `theorem mutualInfo_chain_rule (μ : Measure Ω) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc) : mutualInfo μ (fun ω => (Zc ω, Xs ω)) Yo = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc` | `Common2026/Shannon/CondMutualInfo.lean:222` | 🟢 | 2 変数 chain rule。AWGN converse の **メイン chain rule (n-letter)** には不足、しかし base case として有用。 |

---

## 主要前提条件ボックス (前提事故が起きやすい lemma)

- **`fano_inequality_measure_theoretic` (`Common2026/Fano/Measure.lean:226`)**:
  X 側 `[Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X] [MeasurableSingletonClass X]` (section variable)。`X := Fin M` (M ≥ 2 → Nonempty) で全自動充足。**Y 側無制約** ⇒ `Y := Fin n → ℝ` 直接 OK、T-FFC-1 plumbing 不要。

- **`shannon_converse_single_shot` (`Common2026/Shannon/Converse.lean:81`)**:
  M 側 `[Fintype M] [DecidableEq M] [Nonempty M] [MeasurableSpace M] [MeasurableSingletonClass M]`、**Y 側 `[MeasurableSpace Y]` のみ** (Fano と同型)。
  追加引数 `hMI_finite : mutualInfo μ Msg Yo ≠ ∞` (本 plan で **追加 plumbing ~10-20 行**)。
  `hMsg_uniform : μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count` (uniform W 表現は **`Measure.count` の scalar 倍**形、AWGN converse 構築時に明示)。

- **`differentialEntropy_le_gaussian_of_variance_le` (`Common2026/Shannon/DifferentialEntropy.lean:518`)**:
  4 hypotheses 全列挙: `hμ : μ ≪ volume`, `h_mean : ∫ x, x ∂μ = m`, `h_var : ∫ x, (x - m)^2 ∂μ ≤ (v : ℝ)`, `h_var_int : Integrable (fun x => (x - m)^2) μ`, `h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume`。**`h_ent_int` のみ Mathlib 壁** (negMulLog ∘ rnDeriv の vol-integrability は per-letter Gaussian mixture では Mathlib 標準補題不在) → T-FFC-2 staged 確定。

- **`mutualInfo_le_of_markov` (`Common2026/Shannon/CondMutualInfo.lean:385`)**:
  3 RV `[StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]` (Z 側無制約) + `IsMarkovChain μ Xs Zc Yo` 仮定。`Fin M` は Finite ⇒ StandardBorelSpace 自動、`Fin n → ℝ` は `instStandardBorelSpacePi` 自動 (要再 verbatim 確認、Mathlib 既存)。

- **`mutualInfo_le_sum_per_letter_of_memoryless_strong` (`Common2026/Shannon/CondEntropyMemoryless.lean:552`)**:
  Section variable に **`[Fintype α] [Fintype β]` 等の有限性制約 (`Bridge.lean` entropy 定義の連鎖)** あり ⇒ **AWGN α := β := ℝ で reuse 不可** → **T-FFC-3 staged 確定**。

---

## 自作が必要な要素 (優先度順)

### 1. ★ continuous memoryless MI chain rule `I(X^n;Y^n) ≤ ∑ I(X_i;Y_i)` (T-FFC-3、staged hyp で吸収)

AWGN code (encoder deterministic、Markov chain `X_i ⫫ X_{j≠i} | Z_i` で AWGN は per-letter independent ⇒ `I(X^n;Y^n) = ∑ I(X_i;Y_i)` で **等号** 形まで強くも可) を扱う Mathlib 補題は不在。**bundle `ContinuousMIChainRuleForConverse` の staged hyp として packing** (姉妹 `awgn-mi-decomp-plan.md` の Phase 6 一般 body 補題と相補)。

**推奨実装**: AWGN-agnostic body 補題 `mutualInfo_le_sum_per_letter_for_memoryless_continuous` を別 plan で discharge する (姉妹 `awgn-mi-decomp-plan.md` 拡張 or 新規 plan)。本 plan 内では **bundle hyp に packing するだけ** (~10-30 行で field 定義 + destructure)。

### 2. per-letter integrability `h_ent_int` for Y_i mixture density (T-FFC-2、staged hyp で吸収)

`Integrable (fun y => Real.negMulLog ((μ_{Y_i}.rnDeriv volume y).toReal)) volume` の Mathlib 一般定理は **Gaussian-mixture density (= Gaussian の convex 結合) の negMulLog integrability** であり、Mathlib 不在 ⇒ **bundle `PerLetterIntegrabilityForConverse` の staged hyp として packing**。

**推奨実装**: bundle field を `∀ i : Fin n, Integrable (negMulLog ∘ ...) volume` で全 `Fin n` forall に packing (姉妹 `IsAwgnPowerConstraintHonest` と同型 pattern)。本 plan 内では **field 定義のみ** (~15-30 行)。

### 3. AWGN error probability ↔ Fano `errorProb` bridge

`shannon_converse_single_shot` は **Fano `errorProb μ Msg Yo decoder : ℝ = μ.real {Msg ≠ decoder ∘ Yo}`** を返す。AWGN 結論の `Pe = (1/M) ∑ (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal` との同値性 bridge は **uniform W + product channel `Measure.pi (awgnChannel N h_meas ∘ encoder m)`** から構築可。Mathlib + Common2026 不在の bridge ⇒ **本 plan Phase B-Fano 内で自作 ~25-50 行**。

**推奨実装**: probability-space `Ω := Fin M × (Fin n → ℝ)` (uniform on Fin M × product channel measure) を local 構成、`Msg := Prod.fst`, `Yo := Prod.snd`, `decoder := c.decoder` で `shannon_converse_single_shot` を起動。`Pe` 同値性は Fubini + `Measure.pi`-marginal の標準展開 (~25-40 行)。

---

## 5 判断 (parent plan §Phase 0 Done 条件)

### 判断 #1: bundle field 数 = 3 vs 4

**結論: 3** (per-letter integrability + memoryless chain rule + DPI continuous)。

**根拠**:
- `shannon_converse_single_shot` が **Fano + DPI postprocess + entropy chain + `H(W uniform) = log M`** を 1 補題に集約済 ⇒ bundle 内 4 番目に `EntropyChainRuleForConverse` を入れる必要なし (判断 #2)。
- 元 plan §Approach (line 134-136) の 3 sub-bound `PerLetterIntegrabilityForConverse ∧ ContinuousMIChainRuleForConverse ∧ DPIForConverse` のうち **`DPIForConverse` は in fact genuine 化可** (`mutualInfo_le_of_markov` + `shannon_converse_single_shot` 内部の DPI postprocess で吸収)。
- ⇒ **bundle 内 staged hyp は 2 個** (per-letter integrability + chain rule) **+ DPI continuous は genuine** (bundle field 数 3 のうち 1 つが genuine、staged は 2 つ)。

**alternative**: bundle field 数 を厳密に staged 2 件に絞り、`DPIForConverse` は bundle から外して genuine とする命名 → bundle name は `IsAwgnConverseFeasible` のままで、3 field の連言の **真ん中 1 つ (`DPIForConverse`) を `True` でなく Markov chain hypothesis 形に置換** ([3 hyp の本物連言形]、シンプル)。

**判断**: **bundle field 数 = 3 (PerLetter ∧ Chain ∧ Markov)、うち Chain と PerLetter が staged、Markov は genuine 直接 hypothesis** とする。元 plan の 3-field structure は保持。

### 判断 #2: entropy chain rule + uniform W bridge の在庫

**結論: 完全在庫 (`shannon_converse_single_shot` 内に packaging 済)、本 plan 内で個別補題化不要**。

**根拠**:
- `entropy_of_uniform_msg` (`Converse.lean:56`、private) で `entropy μ Msg = log |M|` が証明済。
- `mutualInfo_eq_entropy_sub_condEntropy` (`Bridge.lean:588`) で entropy chain (`H = I + condEntropy`) も整備済。
- 両者は `shannon_converse_single_shot` 内で完結消費される ⇒ **本 plan が独立に呼ぶ必要なし**。

**Phase B-Fano 戦略の改訂**: 既存 plan の B-Fano-1 (`H(W) = log M`) + B-Fano-2 (entropy chain) を **削除** し、`shannon_converse_single_shot` 1 行呼出 + Pe bridge plumbing のみに圧縮。**B-Fano 規模 ~60-100 行 → ~30-60 行に下方修正**。

### 判断 #3: DPI continuous の壁判定

**結論: 在庫あり、genuine 化可 (T-FFC-3 の DPI 側は staged 不要)**。

**根拠**:
- `mutualInfo_le_of_postprocess` (`DPI.lean:142`) は無 Fintype 制約 ⇒ continuous Y で直接起動可。`shannon_converse_single_shot` 内で消費済。
- `mutualInfo_le_of_markov` (`CondMutualInfo.lean:385`) は X, Y に `[StandardBorelSpace]` のみ ⇒ `Fin M` + `Fin n → ℝ` で全自動。
- **bundle 内 `DPIForConverse` sub-bound は 仮設定** (Markov chain hypothesis 形に置換、genuine)。

**Phase B-DPI 戦略の改訂**: 既存 plan の B-DPI-1 (`I(W; Ŵ) ≤ I(X^n; Y^n)`) を **`shannon_converse_single_shot` 出口の `I(W; Y^n)` 形に直接吸収**。bundle 内 `DPIForConverse` は **Markov chain `IsMarkovChain μ W (encoder ∘ W) Y^n` の genuine hypothesis** に reduce。chain rule との分離 (`I(W;Y^n) ≤ I(X^n;Y^n)`) も `mutualInfo_le_of_markov` で genuine 化 (~30-50 行)。

### 判断 #4: continuous MI chain rule の壁判定

**結論: 壁深度 = large、staged 確定発動 (T-FFC-3)**。

**根拠**:
- 既存 `mutualInfo_le_sum_per_letter_of_memoryless_strong` (`CondEntropyMemoryless.lean:552`) は **`Fintype α` `Fintype β` 制約あり** (`Bridge.lean` entropy 定義の連鎖) → AWGN α := β := ℝ で reuse **不可**。
- `mutualInfo_pi_eq_sum` (`MIChainRule.lean:318`) は無 Fintype だが **`μ.map (Xs i, Ys i)` が iid product joint** 仮定が必要 — AWGN code の non-iid codebook で発火しない。
- `mutualInfo_chain_rule_fin` (`MIChainRule.lean:93`) は **`[Fintype α]` 制約** → 同上で reuse 不可。
- `IsContChannelMIDecompHyp` (`AWGNMIDecompBody.lean:147`) は 1 文字 chain rule (`I(X;Y) = h(Y) − h(Y|X)`)、n 文字 chain rule (`I(X^n;Y^n) ≤ ∑ I(X_i;Y_i)`) ではない。

→ **本 plan の bundle 内 `ContinuousMIChainRuleForConverse` staged hyp 確定発動**。

**集約先 sorry 補題名候補** (orchestrator 検討): `Common2026/Shannon/ContinuousMIChainRule.lean` (新規) で `continuousMI_le_sum_per_letter_memoryless : (mutualInfo μ Xn Yn).toReal ≤ ∑ i, (mutualInfo μ (X i) (Y i)).toReal := sorry @residual(wall:mi-chain-cont)` 形の共有 sorry 補題化 (姉妹 `awgn-mi-decomp-plan.md` Phase 6 と統合可能、もしくは同 plan を本 plan より先に completion させる順序)。本 plan 内では bundle field に閉じ込めるのが最小コスト。

### 判断 #5: per-letter integrability `h_ent_int` の壁形式

**結論: 壁深度 = medium、staged 確定発動 (T-FFC-2)**。

**根拠**:
- `differentialEntropy_le_gaussian_of_variance_le` の `h_ent_int` (`Integrable (fun y => Real.negMulLog ((μ_{Y_i}.rnDeriv volume y).toReal)) volume`) を per-letter で discharge する Mathlib 標準補題は不在。Gaussian density (`integrable_density_log_density_of_gaussian` `DifferentialEntropy.lean:84`) があるが、これは `μ = gaussianReal m v` 形限定。
- AWGN converse の `μ_{Y_i}` は **Gaussian mixture** (X_i は任意分布、Z_i は Gaussian、Y_i = X_i + Z_i ⇒ mixture density `f_{Y_i}(y) = ∫ ϕ(y-x; 0, N) dμ_{X_i}(x)`) ⇒ density の振る舞いは Gaussian と同質 (有界 + 急減衰) だが Mathlib lemma で直接吸えない。

→ bundle 内 `PerLetterIntegrabilityForConverse` staged hyp 確定発動。**packing 形式**: `∀ i : Fin n, Integrable (fun y => Real.negMulLog ((μ_{Y_i}.rnDeriv volume y).toReal)) volume` で全 `Fin n` forall (姉妹 `IsAwgnPowerConstraintHonest` と同型 pattern)。**field 構造**: 4 mathlib max-entropy hyp のうち 3 (mean=0, var ≤ P+N, h_var_int) を bundle field に併せて持つか、それとも `h_ent_int` のみ持って残 3 hyp を本 plan で genuine 化するかは Phase A 着手時の細則 (in inventory): per-letter input `E[X_i²] ≤ P` は power constraint + uniform W で genuine 化可 (~20 行)、`μ_{Y_i} ≪ volume` は Gaussian convolution で genuine ⇒ **bundle に持たせるのは `h_ent_int` のみが最小**。

---

## 規模 (判断 #5 補完: Phase 別工数感)

| Phase | 内容 | 楽観 | 中央 | 悲観 (壁発動) |
|---|---|---:|---:|---:|
| Phase A | skeleton + bundle predicate (3 field, 1 genuine + 2 staged) | 60 | 100 | 150 |
| Phase B-Fano | `shannon_converse_single_shot` 呼出 + Pe bridge plumbing | 30 | 60 | 100 |
| Phase B-DPI/Markov | `mutualInfo_le_of_markov` 経由 `I(W;Y^n) ≤ I(X^n;Y^n)` (genuine) | 40 | 70 | 120 |
| Phase B-chain (staged) | bundle destructure + `I(X^n;Y^n) ≤ ∑ I(X_i;Y_i)` (staged hyp ↦ direct) | 20 | 40 | 60 |
| Phase B-Gaussian | per-letter mean/var/conv 計算 + `differentialEntropy_le_gaussian_of_variance_le` (h_ent_int staged) | 100 | 150 | 220 |
| Phase C 統合 + Phase V | wrapper + `awgn_converse` body 置換 | 30 | 50 | 80 |
| skeleton plumbing 部分 | (各 Phase の skeleton 部分) | 30 | 50 | 80 |
| **合計** | | **~310** | **~520** | **~810** |

**中央予測 ~520 行** (plan 中央予測 ~650 行から下方修正、`shannon_converse_single_shot` 既存吸収による)。
**T-FFC-4 (~1000 行超過) 発動確率**: 低 (悲観 ~810 行)。**2 file 分割不要見込み**。

---

## 撤退ラインへの距離

| 撤退ライン | 発動可否 | 縮退案・現状 |
|---|---|---|
| **T-FFC-1** (`[StandardBorelSpace (Fin n → ℝ)]` 自動推論失敗) | **発動しない** | `fano_inequality_measure_theoretic` も `shannon_converse_single_shot` も Y 側無制約 ⇒ plumbing 不要 |
| **T-FFC-2** (per-letter integrability Mathlib 壁) | **確定発動** | bundle `PerLetterIntegrabilityForConverse` staged hyp で packing (判断 #5)。本 plan 完了で残置 |
| **T-FFC-3** (continuous MI chain rule Mathlib 壁) | **確定発動** | bundle `ContinuousMIChainRuleForConverse` staged hyp で packing (判断 #4)。本 plan 完了で残置、姉妹 `awgn-mi-decomp-plan.md` Phase 6 完了で discharge 候補 |
| **T-FFC-4** (規模超過 ~1000 行) | **発動しない見込み** | 中央 ~520 行 / 悲観 ~810 行で 1000 行未満 |

**新規撤退ライン提案** (本 inventory 由来):

- **T-FFC-5 (Pe bridge 自作肥大)**: `shannon_converse_single_shot` の Fano `errorProb` と AWGN `(1/M) ∑ errorProbAt m` の同値性 bridge plumbing が 50+ 行に膨張した場合 → Phase B-Fano の B-Fano-3 を **独立補題化** (`awgn_errorProb_eq_fano_errorProb`) し、本 plan 内では 1 行呼出に。判断ログで記録。

---

## 着手 skeleton (`Common2026/Shannon/AWGNConverseDischarge.lean`)

新規ファイルの **出だし 20-30 行** (本 plan Phase A の skeleton 部分、本 inventory は実装しないので **参考のみ**)。

```lean
import Common2026.Meta.EntryPoint
import Common2026.Shannon.AWGN
import Common2026.Shannon.AWGNConverse          -- sorry 置換のため
import Common2026.Shannon.Converse              -- shannon_converse_single_shot
import Common2026.Shannon.MutualInfo            -- mutualInfo typed RV
import Common2026.Shannon.CondMutualInfo        -- IsMarkovChain / mutualInfo_le_of_markov
import Common2026.Shannon.DifferentialEntropy   -- differentialEntropy_le_gaussian_of_variance_le
import Common2026.Shannon.ChannelCoding         -- errorProbAt / Channel / outputDistribution
import Common2026.Fano.Measure                  -- errorProb / condEntropy / fano_inequality
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# AWGN converse discharge (F-3 analytic body)

`awgn_converse` (`AWGNConverse.lean:59-70`) body sorry を analytic body で埋める。
姉妹 `AWGNAchievabilityDischarge.lean` (1641 行) と対称の **bundle-predicate packing**。

3 sub-bound bundle `IsAwgnConverseFeasible`:
* per-letter integrability (Mathlib 壁、staged) — `PerLetterIntegrabilityForConverse`
* continuous MI memoryless chain rule (Mathlib 壁、staged) — `ContinuousMIChainRuleForConverse`
* DPI via Markov chain `W → X^n → Y^n` (genuine、Common2026 既存補題で discharge) — `MarkovChainForConverse`
-/

namespace InformationTheory.Shannon.AWGN

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

-- Phase A skeleton (3 field bundle、判断 #1)
def PerLetterIntegrabilityForConverse (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) {M n : ℕ} (c : AwgnCode M n P) : Prop := by sorry
-- @residual(wall:awgn-converse-perletter-integrability)

def ContinuousMIChainRuleForConverse (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) {M n : ℕ} (c : AwgnCode M n P) : Prop := by sorry
-- @residual(wall:mi-chain-cont)

def MarkovChainForConverse (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) {M n : ℕ} (c : AwgnCode M n P) : Prop := by sorry
-- @residual(plan:awgn-converse-aux-plan) -- genuine 化候補、Phase A-2 で再判定

def IsAwgnConverseFeasible (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ {M n : ℕ} (_hM : 2 ≤ M) (c : AwgnCode M n P),
    PerLetterIntegrabilityForConverse P N h_meas c ∧
    ContinuousMIChainRuleForConverse P N h_meas c ∧
    MarkovChainForConverse P N h_meas c

@[entry_point]
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
  sorry  -- @residual(plan:awgn-converse-aux-plan)

end InformationTheory.Shannon.AWGN
```

---

## 検証手順 (再現性)

### loogle queries (verbatim 記録)

- `ProbabilityTheory.gaussianReal_conv_gaussianReal` → Found 1 (Mathlib `Real.lean:613`)
- `ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun` → Found 1 (Mathlib `Real.lean:624`)
- `MeasureTheory.integral_rnDeriv_smul` → Found 1 (Mathlib `RadonNikodym.lean`)
- `ProbabilityTheory.IndepFun` → Found 173 (多数)
- `MeasureTheory.Measure.pi` → Found 127 (多数)

### rg 探索 pattern (Common2026/) — 主要ヒット箇所

- `mutualInfo_le_of_postprocess` → `Common2026/Shannon/DPI.lean:142`
- `mutualInfo_le_of_markov` → `Common2026/Shannon/CondMutualInfo.lean:385`
- `IsMarkovChain` → `Common2026/Shannon/CondMutualInfo.lean:73`
- `mutualInfo_chain_rule\b` → `Common2026/Shannon/CondMutualInfo.lean:222`
- `mutualInfo_chain_rule_fin` → `Common2026/Shannon/MIChainRule.lean:93` (Fintype α 制約)
- `mutualInfo_pi_eq_sum` → `Common2026/Shannon/MIChainRule.lean:318` (iid joint 仮定必要)
- `mutualInfo_le_sum_per_letter_of_memoryless_strong` → `Common2026/Shannon/CondEntropyMemoryless.lean:552` (Fintype α 制約)
- `fano_inequality_measure_theoretic` → `Common2026/Fano/Measure.lean:226`
- `shannon_converse_single_shot` → `Common2026/Shannon/Converse.lean:81`
- `shannon_converse_single_shot_markov_encoder` → `Common2026/Shannon/Converse.lean:155` (encoder Markov chain 版、本 plan で参考可)
- `differentialEntropy_le_gaussian_of_variance_le` → `Common2026/Shannon/DifferentialEntropy.lean:518`
- `differentialEntropy_gaussianReal` → `Common2026/Shannon/DifferentialEntropy.lean:412`
- `awgnChannel_apply_absolutelyContinuous` → `Common2026/Shannon/AWGNMIDecompBody.lean:103`
- `entropy_of_uniform_msg` → `Common2026/Shannon/Converse.lean:56` (private)
- `mutualInfo_eq_entropy_sub_condEntropy` → `Common2026/Shannon/Bridge.lean:588`

### 参考にしなかった (scope 外 / 無関係)

- `IsContChannelMIDecompHyp` (`AWGNMIDecompBody.lean:147`) — 1 文字 chain rule、n 文字 chain rule とは独立
- `channel_coding_converse_general_memoryless_strong` (`ChannelCodingConverseGeneralStrong.lean:276`) — `Fintype α` 制約で AWGN 非対応
- `Common2026/Shannon/ChannelCodingConverseGeneralComplete.lean` — 同上

### parent plan §Phase 0 verbatim 確認済補題 (本 inventory 再確認実施)

- `fano_inequality_measure_theoretic` (`Fano/Measure.lean:226`) — section variable + 4 args + hcard、結論 `condEntropy ≤ binEntropy + Pe·log(card-1)`。verbatim 確認済 (上 §A)。
- `differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:518`) — 4-hyp 形 (`hμ`, `h_mean`, `h_var ≤ v`, `h_var_int`, `h_ent_int`)、結論 `differentialEntropy ≤ (1/2) log(2πev)`。verbatim 確認済 (上 §E)。
- `differentialEntropy_gaussianReal` (`DifferentialEntropy.lean:412`) — closed form `(1/2) log(2πev)`。verbatim 確認済。
- `mutualInfoOfChannel` (`ChannelCoding.lean:85`) — `klDiv (jointDistribution p W) (p.prod (outputDistribution p W))` 形。verbatim 確認済。
- `AwgnCode` (`AWGN.lean:98`) — encoder/decoder/decoder_meas/power_constraint 4 field。verbatim 確認済。
