# EPI G2 連続性壁 — Mathlib + InformationTheory API 在庫調査

> 攻略対象: `t ↦ entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z ω))` の `t` 連続性、特に端点 `t = 0⁺` への収束。
> 親計画: [`docs/shannon/epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md)（撤退ライン **L-Concl-A-θ (G2)**）。
> 対象 `sorry`: `InformationTheory/Shannon/EPIStamToBridge.lean:1173` `csiszarGap1Source_continuousOn`（`@residual(plan:epi-stam-to-conclusion-phaseA-plan)` — sub-step A-4-continuity）。

## 一行サマリ

**外側合成 (log/exp/sub/HasDerivAt 橋)・DCT パラメータ連続性 API・gaussian var→0 (= Dirac) は 100% 既存。`differentialEntropy` / `entropyPower` の連続性・半連続性は Mathlib にも InformationTheory にも完全不在 (loogle Found 0)。G2 の核は「DCT の一様可積分 dominating bound を heat-flow 密度に対して `t=0⁺` で供給する」点に集約され、これは Mathlib 壁ではなく自作 1 件（heat-flow 密度の一様可積分性 + 端点連続性）。撤退ライン L-Concl-A-θ は条件付きで発動回避可能。**

---

## 主定理の最終形（再掲）

`InformationTheory/Shannon/EPIStamToBridge.lean:1173`（verbatim）:

```lean
theorem csiszarGap1Source_continuousOn
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_reg_sum : …EPIStamDischarge.IsDeBruijnRegularityHyp
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_X : …IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y : …IsDeBruijnRegularityHyp Y Z_Y P) :
    ContinuousOn (fun t : ℝ => csiszarGap1Source X Y Z_X Z_Y P t) (Set.Ici (0 : ℝ))
```

`csiszarGap1Source`（`EPIL3Integration.lean:1358`、verbatim）:

```lean
noncomputable def csiszarGap1Source … (t : ℝ) : ℝ :=
  entropyPower (P.map (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω)))
    - entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω))
    - entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω))
```

`entropyPower`（`EntropyPowerInequality.lean:101`）= `Real.exp (2 * differentialEntropy μ)`。
`differentialEntropy`（`DifferentialEntropy.lean:45`）= `∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume`。

証明戦略（pseudo-Lean）:

```
-- (A) 内部 t > 0: 既存 HasDerivAt から無料で連続
intro t ht; rcases eq_or_lt_of_le ht with rfl | ht_pos
-- (B-interior) t > 0:
--   (csiszarGap1Source_hasDerivAt … ht_pos).continuousAt.continuousWithinAt
-- (B-endpoint) t = 0:  ← ここが G2 の核
--   各 entropyPower (P.map (· + √t Z)) = exp(2 ∫ negMulLog f_t dx)
--   ContinuousWithinAt.exp ∘ (·2·) ∘ continuousWithinAt_of_dominated
--   要: t-一様 integrable bound `bound x` s.t. ‖negMulLog f_t x‖ ≤ bound x  ∀ t∈Ici 0 near 0
--   + ∀ᵐ x, ContinuousWithinAt (t ↦ negMulLog f_t x) (Ici 0) 0
--   注意: t=0⁺ で gaussianReal 0 (s·) → Dirac (gaussianReal_zero_var) なので
--         密度 f_t は退化方向。一様 bound が core difficulty。
```

---

## API 在庫テーブル

### 1. 微分エントロピー / entropyPower の連続性・半連続性 — ❌ **完全不在 (真 wall 候補)**

| 概念 | Mathlib API | file:line | 状態 | G2 での扱い |
|---|---|---|---|---|
| `differentialEntropy` の連続性 | — | — | ❌ **不在** (InformationTheory 内 `rg` Found 0) | 自作。DCT 経由で組む |
| `entropyPower` の連続性 | — | — | ❌ **不在** (内部唯一の言及は対象 `sorry` の docstring `EPIStamToBridge.lean:1158-1164`) | 自作 |
| `klDiv` の lower semicontinuity | — | — | ❌ **不在** (loogle `LowerSemicontinuous, InformationTheory.klDiv` → **Found 0**) | 使わない |
| `klDiv` の tendsto/連続性 | — | — | ❌ **不在** (loogle `InformationTheory.klDiv, Filter.Tendsto` → **Found 0**) | 使わない |
| 測度のエントロピー連続性 (`MeasureTheory`) | — | — | ❌ Mathlib に entropy-of-measure 連続性 API 自体が存在しない | — |

> **重要**: 微分エントロピーは弱収束に対し連続ではなく **下半連続止まり**（一般論）。Mathlib にはその下半連続性すら無い。よって「弱収束 → entropyPower 収束」は **直接は使えない**。端点収束は密度レベルの DCT で個別に組む必要がある（下記 3）。

### 2. Gaussian smoothing / 消えゆく noise の収束 — ✅ **primitive 既存、weak-conv 機構あり**

| 概念 | Mathlib API | file:line | signature (verbatim) | 状態 |
|---|---|---|---|---|
| var→0 = Dirac | `ProbabilityTheory.gaussianReal_zero_var` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:207` | `(μ : ℝ) : gaussianReal μ 0 = Measure.dirac μ` | ✅ |
| 定数倍 push-forward | `ProbabilityTheory.gaussianReal_map_const_mul` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:298` | `(c : ℝ) : (gaussianReal μ v).map (c * ·) = gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)` | ✅ HeatFlowPath.lean:84 で既使用 |
| 弱収束（測度列の tendsto） | `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` ほか 37 件 | `Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean` | weak-* topology (テスト関数積分) | ✅ 機構あり |
| push-forward の弱連続性 | `MeasureTheory.ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous` | `Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean` | `Tendsto μs → Continuous f → Tendsto (μs.map f)` | ✅ |
| gaussian の tendsto (var→0 弱収束を直接述べた lemma) | — | — | ❌ **不在** (loogle `ProbabilityTheory.gaussianReal, Filter.Tendsto` → **Found 0**) | 自作なら可（→ Dirac へ） |
| dirac への weak tendsto | — | — | ❌ **不在** (loogle `Filter.Tendsto, MeasureTheory.Measure.dirac` → **Found 0**) | — |

> **判定**: `gaussianReal_zero_var` により「`t→0⁺` で noise gaussian は Dirac に潰れる」は等式で確定。弱収束機構（portmanteau / ProbabilityMeasure topology）も完備。ただし **弱収束は entropyPower 収束を与えない**（上記 1）。よって 2 のルートは「測度がどこへ行くか」までで、entropyPower への lift は 3 が握る。

### 3. Dominated convergence / 積分のパラメータ連続性 — ✅ **DCT 連続性 API 完備（核）**

文脈型クラス（`Bochner/Basic.lean:156` + `:438`）: `{G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]`、`{X : Type*} [TopologicalSpace X] [FirstCountableTopology X]`、`μ : Measure α`。`G := ℝ` が条件を満たすので real-valued エントロピー積分に適用可。

| API | file:line | signature (verbatim、結論型含む) | G2 での扱い |
|---|---|---|---|
| `MeasureTheory.continuousAt_of_dominated` | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:451` | `{F : X → α → G} {x₀ : X} {bound : α → ℝ} (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a) (bound_integrable : Integrable bound μ) (h_cont : ∀ᵐ a ∂μ, ContinuousAt (fun x => F x a) x₀) : ContinuousAt (fun x => ∫ a, F x a ∂μ) x₀` | 内部 `t>0` 用（ただし内部は HasDerivAt で済むので主に端点用 within 版を使う） |
| **`MeasureTheory.continuousWithinAt_of_dominated`** | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:440` | `{F : X → α → G} {x₀ : X} {bound : α → ℝ} {s : Set X} (hF_meas : ∀ᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) μ) (h_bound : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a) (bound_integrable : Integrable bound μ) (h_cont : ∀ᵐ a ∂μ, ContinuousWithinAt (fun x => F x a) s x₀) : ContinuousWithinAt (fun x => ∫ a, F x a ∂μ) s x₀` | **端点 `t=0⁺` on `Set.Ici 0` 用の第一候補。`ContinuousOn` は各点 `ContinuousWithinAt` に分解できるのでこれ 1 本で endpoint も interior も賄える** |
| `MeasureTheory.continuousOn_of_dominated` | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:462` | `{F : X → α → G} {bound : α → ℝ} {s : Set X} (hF_meas : ∀ x ∈ s, AEStronglyMeasurable (F x) μ) (h_bound : ∀ x ∈ s, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a) (bound_integrable : Integrable bound μ) (h_cont : ∀ᵐ a ∂μ, ContinuousOn (fun x => F x a) s) : ContinuousOn (fun x => ∫ a, F x a ∂μ) s` | `Set.Ici 0` 全体で一様 bound が取れれば一発（最有力だが bound が最強の要求） |
| `MeasureTheory.continuous_of_dominated` | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:473` | `{F : X → α → G} {bound : α → ℝ} (hF_meas : ∀ x, AEStronglyMeasurable (F x) μ) (h_bound : ∀ x, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a) (bound_integrable : Integrable bound μ) (h_cont : ∀ᵐ a ∂μ, Continuous fun x => F x a) : Continuous fun x => ∫ a, F x a ∂μ` | 全域連続が要るとき（端点 within で十分なら不要） |

> **判定**: DCT パラメータ連続性は **完全に既存**。G2 が「Mathlib 壁」かどうかは、この `bound : α → ℝ`（`t` に依存しない一様 integrable 関数）を heat-flow 密度 `f_t(x) = (P.map(X+√t Z)).rnDeriv volume x` に対し `t=0⁺` 近傍で供給できるかに **完全に還元される**。供給できれば G2 は Mathlib 壁ではなく自作 plumbing。供給できなければ（密度が `t→0` で集中・退化し一様 bound が破綻）真 wall。

### 4. 合成の連続性（外側 log / exp / sub）— ✅ **完全既存**

| API | file:line | signature (verbatim) | 正値性 precondition |
|---|---|---|---|
| `Real.continuous_exp` | `Mathlib/Analysis/SpecialFunctions/Exp.lean` | `Continuous Real.exp` | なし。`entropyPower = exp(2·h)` の外側は無条件連続 |
| `Real.continuousOn_log` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:352` | `ContinuousOn Real.log {0}ᶜ` | `≠ 0` (log-ratio gap 版で必要) |
| `ContinuousOn.log` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:491` | `(hf : ContinuousOn f s) (h₀ : ∀ x ∈ s, f x ≠ 0) : ContinuousOn (fun x => log (f x)) s` | `∀ x ∈ s, f x ≠ 0`（`entropyPower_pos`/`add_pos` で供給可） |
| `ContinuousOn.sub` | `Mathlib/Topology/ContinuousOn` (`ContinuousOn.sub`) | `ContinuousOn f s → ContinuousOn g s → ContinuousOn (f - g) s` | なし |
| `ContinuousOn.add` | 同上 | 同様 | なし |
| `ContinuousWithinAt.exp` / `Continuous.comp` | `Mathlib/Analysis/SpecialFunctions/Exp` | `exp ∘ (continuous)` 合成 | なし |

> **判定**: `csiszarGap1Source`（差分形）の外側は `exp` + `sub` のみ → 正値性すら不要、3 で各 entropyPower 項が連続なら自動。`csiszarLogRatioGap`（log-ratio 形）の外側は `log` + `sub` で `≠ 0` が要るが `entropyPower_pos`（`EntropyPowerInequality.lean:108`、`@audit:ok`）と `add_pos` で供給可。**外側合成は全く壁にならない。**

### 5. HasDerivAt → ContinuousOn 橋（内部 `t>0` を無料化）— ✅ **完全既存 + genuine 供給元あり**

| API | file:line | signature (verbatim) | G2 での扱い |
|---|---|---|---|
| `HasDerivAt.continuousAt` | `Mathlib/Analysis/Calculus/Deriv/Basic.lean:845` | `(h : HasDerivAt f f' x) : ContinuousAt f x` | 内部 `t>0` 連続を即出す |
| `DifferentiableOn.continuousOn` | `Mathlib/Analysis/Calculus/FDeriv/Basic.lean:658` | `(h : DifferentiableOn 𝕜 f s) : ContinuousOn f s` | `interior (Ici 0) = Ioi 0` 上の連続を一括供給 |
| `ContinuousAt.continuousWithinAt` | Mathlib `Topology` | `ContinuousAt f x → ContinuousWithinAt f s x` | interior 点を `ContinuousOn` に編入 |
| **供給元** `csiszarGap1Source_hasDerivAt` | `InformationTheory/Shannon/EPIStamToBridge.lean:476` | `… {t : ℝ} (ht : 0 < t) : HasDerivAt (fun s => csiszarGap1Source … s) (…) t`（genuine、`sorry` は被呼出 de Bruijn 壁が保持、本補題は `@residual` 無し） | **内部 `t>0` 連続性は完全に無料で出る** |
| `csiszarGap1Source_differentiableOn_interior` | `InformationTheory/Shannon/EPIStamToBridge.lean:1186` | `… : DifferentiableOn ℝ (fun t => csiszarGap1Source … t) (interior (Set.Ici 0))`（**証明済み、`sorry` 無し**、本体は HasDerivAt 経由） | interior 連続は **既にこの補題が握っている** |

> **判定**: G2 のうち **内部 `t>0` は既に解決済み**（`csiszarGap1Source_differentiableOn_interior` が `interior (Ici 0)` 上連続を供給。`DifferentiableOn.continuousOn` で `ContinuousOn (Ioi 0)` 即出）。残る未解決は **端点 `t=0` のみ**。よって G2 の真の困難は「`ContinuousWithinAt (Ici 0) 0`」1 点に縮退する。

---

## 主要前提条件ボックス（事故が起きやすい lemma）

- **`continuousWithinAt_of_dominated` / `continuousOn_of_dominated`** の核心前提:
  - `bound : α → ℝ` は **`x`(パラメータ `t`) に依存しない単一の integrable 関数**。`h_bound : ∀ᶠ t in 𝓝[Ici 0] 0, ∀ᵐ a, ‖F t a‖ ≤ bound a`。→ heat-flow 密度 `negMulLog f_t` に対し **`t=0⁺` 近傍で一様な dominating bound** を作るのが全て。`f_t` は `t→0` で Dirac へ集中（`gaussianReal_zero_var`）するため、`negMulLog f_t` が `+∞` 方向に振れないことを示す必要がある。**ここが G2 の唯一の数学的内容。**
  - `bound_integrable : Integrable bound μ`（= `volume`）。Lebesgue 測度上の可積分性。
  - `h_cont : ∀ᵐ a ∂μ, ContinuousWithinAt (fun t => F t a) (Ici 0) 0`。各点 `x` で `t ↦ negMulLog f_t(x)` が `t=0⁺` で連続（density の連続依存）。
  - `G := ℝ` は `[NormedAddCommGroup ℝ] [NormedSpace ℝ ℝ]` を満たす（無問題）。`X := ℝ`(=`t` の空間) は `[TopologicalSpace] [FirstCountableTopology]` を満たす（無問題）。
- **`gaussianReal_zero_var`**: `gaussianReal μ 0 = Measure.dirac μ`。`t=0⁺` の極限測度は **Dirac**。このとき `differentialEntropy (Dirac) = 0`（`DifferentialEntropy.lean:155` verbatim 確認済）、`entropyPower (Dirac) = exp 0 = 1`。**ただし `csiszarGap1Source` の `t=0` 値は noise 無し測度 `P.map X` 等の entropyPower**（`csiszarGap1Source` の `√0 = 0` で noise 項消滅、`P.map X` 自身が連続体なら退化しない）であり、Dirac へ潰れるのは noise factor `gaussianReal 0 (s·)` のみ。`P.map (X+√t Z)` 自体は `X` が連続分布なら `t=0` でも連続分布 `P.map X`。→ **端点で測度が Dirac に潰れる事故は起きない**（noise が消えるだけ）。この区別が L-DBD 型 drift 防止の要。
- **`ContinuousOn.log` の `≠ 0`**: log-ratio 版を使う場合のみ。差分版 `csiszarGap1Source` は `exp+sub` なので不要。

---

## 自作が必要な要素（優先度順）

1. **【最優先・G2 核】heat-flow 密度の `t=0⁺` 一様可積分性 + 端点連続性**
   - 推奨実装: `F t x := Real.negMulLog ((P.map (fun ω => X ω + √t * Z ω)).rnDeriv volume x).toReal` に対し `continuousWithinAt_of_dominated` の 4 前提（measurability / 一様 bound / bound 可積分 / 各点 within 連続）を供給する補題群。
   - 工数感: **大（50–120 行）**。bound 構成（heat-flow 密度の sup or `t`-一様 Gaussian tail bound）が最重く、`IsDeBruijnRegularityHyp` bundle に density-path 連続性を追加するか別 regularity hyp が要る可能性。
   - 落とし穴: `negMulLog` は `f=0` で `0` だが `f→0⁺` で `-f log f → 0` のため `‖negMulLog f‖` は有界化容易、一方 `f` が大きい領域（Dirac 接近で密度が尖る noise 側）の bound が `t→0` で破綻しうる。**ただし上記ボックス通り noise が消えるだけで `P.map X` 側は退化しないので、bound は `P.map X` の密度近傍で取れる見込み。**

2. **【中】`entropyPower` の連続性ラッパー** `t ↦ entropyPower (P.map …)` = `exp ∘ (2·) ∘ (∫ negMulLog f_t)` の合成
   - 推奨実装: 1 の `ContinuousWithinAt (∫ …)` を `Real.continuous_exp.comp` / `ContinuousWithinAt.const_mul` で lift。工数 **小（10–20 行）**、1 が出れば機械的。

3. **【小】内部 + 端点の `ContinuousOn (Ici 0)` 組み立て**
   - 内部は `csiszarGap1Source_differentiableOn_interior`（既証明）→ `DifferentiableOn.continuousOn`、端点は 2。`ContinuousOn` を「interior は微分から、端点 0 は within-DCT から」で 2 ケース貼り合わせ。工数 **小（15–25 行）**。

---

## Mathlib 壁の列挙（真に不在 = `@residual(wall:...)` 対象候補）

| wall 候補 | loogle 確認 | 真壁か |
|---|---|---|
| `differentialEntropy`/`entropyPower` の連続性・半連続性 | InformationTheory 内 `rg` で実体 0、Mathlib に measure-entropy 連続性 API 自体無し | **真の不在だが自作可能**（DCT で組める）。Mathlib 壁ではなく自作 plumbing |
| `klDiv` lower semicontinuity | loogle `LowerSemicontinuous, InformationTheory.klDiv` → **Found 0** | 真の不在（だが G2 では不要） |
| `klDiv` の tendsto/連続性 | loogle `InformationTheory.klDiv, Filter.Tendsto` → **Found 0** | 真の不在（G2 では不要） |
| gaussian var→0 の弱収束 lemma | loogle `ProbabilityTheory.gaussianReal, Filter.Tendsto` → **Found 0** | 真の不在（だが `gaussianReal_zero_var` 等式で代替可） |

> **結論**: G2 に「真の Mathlib 壁」は **存在しない**。一見壁に見える「entropy 連続性」は DCT 連続性 API（既存）+ 一様 bound（自作）で組める。`@residual(wall:...)` の新規 register は **不要**。現 `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` のままで closure plan に乗せるのが正しい分類。
>
> **shared sorry 補題化推奨**: 同種の「heat-flow 密度パラメータ連続性 / 一様可積分性」は EPI 系の複数 file（`csiszarGap1Source_continuousOn`、`csiszarLogRatioGap_continuousOn` `EPIStamToBridge.lean:1030`、`EPIStamToBridge.lean:1042` の transitive consumer）で同一壁を共有している。1 本の共有補題 `heatFlowEntropyPower_continuousWithinAt`（仮称）に集約し、差分版・ratio 版双方がそれを呼ぶ形を推奨（`docs/audit/audit-tags.md`「共有 Mathlib 壁: shared sorry 補題パターン」）。

---

## 撤退ラインへの距離

親計画 `epi-stam-to-conclusion-plan.md:311`:

> **L-Concl-A-θ** (G2): heat-flow 連続性 DCT 不在 → `@residual(wall:...)` 化、closure 分離

**判定: 条件付きで発動回避可能（DCT API は不在ではなく完備）。**

- L-Concl-A-θ の発動条件「DCT 不在」は **誤前提**: `continuousWithinAt_of_dominated` 等は完備（カテゴリ 3）。よって「DCT 不在ゆえ即 `@residual(wall:...)`」のシナリオは成立しない。
- ただし発動の **実質条件**は「heat-flow 密度に `t=0⁺` 一様 integrable bound が作れるか」に移る。これが当該セッションで作れない場合は **honest に `sorry` 継続**（現 `@residual(plan:...)` 維持、`wall:` 昇格は不要 — 自作可能性が残るため）。
- **新規撤退ライン提案（L-Concl-A-θ 縮退版）**:
  - **L-Concl-A-θ′**: 端点 `t=0⁺` の一様 bound 構成が 1 セッション（〜120 行）で完了しない場合 → `csiszarGap1Source_continuousOn` の端点ケースのみ `sorry + @residual(plan:epi-stam-to-conclusion-phaseA-plan)` 継続、**内部 `t>0` 連続性は既証明 `csiszarGap1Source_differentiableOn_interior` から genuine に部分達成**として分離公開（honest 命名、仮説束化禁止）。
  - 撤退口は **sorry + `@residual`**（仮説 bundling 禁止）。

---

## 着手 skeleton

`InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean`（または `EPIStamToBridge.lean` 内拡張）の出だし:

```lean
import Mathlib.MeasureTheory.Integral.Bochner.Basic        -- continuousWithinAt_of_dominated
import Mathlib.Probability.Distributions.Gaussian.Real     -- gaussianReal_zero_var
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog      -- negMulLog
import Mathlib.Analysis.SpecialFunctions.Exp                -- Real.continuous_exp
import Mathlib.Analysis.Calculus.Deriv.Basic                -- HasDerivAt.continuousAt
import InformationTheory.Shannon.EntropyPowerInequality     -- entropyPower, entropyPower_pos
import InformationTheory.Shannon.DifferentialEntropy        -- differentialEntropy
import InformationTheory.Shannon.EPIL3Integration           -- csiszarGap1Source

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]

/-- **G2 核**: heat-flow 密度の被積分関数 `negMulLog f_t` は `t=0⁺` 近傍で
`t`-一様 integrable bound を持つ。`continuousWithinAt_of_dominated` の `h_bound`
を供給する。-/
theorem heatFlowDensity_uniform_bound :
    True := by
  sorry  -- @residual(plan:epi-stam-to-conclusion-phaseA-plan) -- G2 endpoint uniform bound

/-- **G2 ラッパー**: `t ↦ entropyPower (P.map (X + √t Z))` は `Set.Ici 0` 上
`t=0⁺` で `ContinuousWithinAt`。`continuousWithinAt_of_dominated` + `Real.continuous_exp` 合成。-/
theorem heatFlowEntropyPower_continuousWithinAt :
    ContinuousWithinAt
      (fun t : ℝ => entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z ω)))
      (Set.Ici (0 : ℝ)) 0 := by
  sorry  -- @residual(plan:epi-stam-to-conclusion-phaseA-plan) -- G2 endpoint continuity

end InformationTheory.Shannon
```

> skeleton の `True` placeholder は inventory 例示用。実装時は `h_bound` の述語型（`∀ᶠ t in 𝓝[Ici 0] 0, ∀ᵐ x, ‖negMulLog f_t x‖ ≤ bound x`）を本来形で書き、body `sorry`。`Prop := True` を残置してはいけない（tier 5）。

---

## 検証メモ（verbatim 確認済の境界値）

- `differentialEntropy (Measure.dirac m) = 0`（`DifferentialEntropy.lean:155` Read 済）→ `entropyPower (dirac) = exp 0 = 1`。直感「−∞ / 0」は誤り（CLAUDE.md 注意事項通り）。
- `gaussianReal μ 0 = Measure.dirac μ`（`Real.lean:207` Read 済）。`t=0` で潰れるのは **noise factor のみ**、`csiszarGap1Source` の各 entropyPower 引数 `P.map(X+√0·Z) = P.map X` は元測度の push-forward で退化しない。よって端点で gap が退化定数化する事故（L-DBD 型）は起きない。
- 内部 `t>0` 連続性は `csiszarGap1Source_differentiableOn_interior`（`EPIStamToBridge.lean:1186`、`sorry` 無しで証明済）が既に供給。G2 残課題は端点 1 点。
