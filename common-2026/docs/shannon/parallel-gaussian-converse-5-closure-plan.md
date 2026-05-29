# Parallel Gaussian ② converse — #5 joint log-density integrability closure サブ計画

> **Parent**: [`parallel-gaussian-converse-closure-plan.md`](parallel-gaussian-converse-closure-plan.md)
> — 親計画の Phase 1 はほぼ完了し、残るは **唯一の residual #5**
> `parallelOutput_joint_logDensity_integrable` のみ。本 sub-plan はその #5 専用 closure 計画。
> **Inventory (SoT)**: [`parallel-gaussian-converse-multivariate-mi-api-inventory.md`](parallel-gaussian-converse-multivariate-mi-api-inventory.md)
> — 全建材マップ・skeleton・落とし穴の verbatim 在庫。本 plan はそれを実行可能な Phase 分解 + 撤退口に変換したもの。
> **1-D 手本 (SoT)**: `Common2026/Draft/Shannon/AwgnCapacityConverseMaxent.lean` Phase 6 (`:333-714`)。

<!--
記法: 状態絵文字 📋/🚧/✅/🔄、取り消し線で廃止 Phase、判断ログ append-only。
本 plan は docs-only。Lean 実装は lean-implementer に dispatch。
plan filename stem = `parallel-gaussian-converse-5-closure-plan`。
着手中・着地中の self-build 残課題は @residual(plan:parallel-gaussian-converse-5-closure-plan) で参照する。
-->

## 進捗 — ✅ 完了 (2026-05-29、全 Phase genuine、#5 proof done、headline sorryAx-free)

- [x] M0 在庫照合 + wall/plan 再裁定の確定 (独立 auditor) ✅ — self-buildable 確定、`wall:multivariate-mi`→`plan:...` reclassify
- [x] Phase 1 — 多変量 mixture density def + withDensity 等式 (在庫項目 1) ✅
- [x] Phase 2 — 上界 (容易) + 座標箱 Chebyshev (在庫項目 3) ✅
- [x] Phase 3 — ★ 下界 (Gaussian tail 座標積、最重量、在庫項目 2 下界部) ✅ — 撤退口未使用、genuine
- [x] Phase 4 — log 絶対値 quadratic 包絡合成 (在庫項目 2 合成部) ✅
- [x] Phase 5 — #5 本体 joint integrable 締め (在庫項目 4) ✅
- [x] Phase 6 — 独立 honesty 監査 + `@audit:ok` 付与 ✅ — 9 declaration ok / defect 0、n=0 退化 honest 確認、#print axioms 独立確認

**結果**: `parallelOutput_joint_logDensity_integrable` 0 sorry / 0 residual / `@audit:ok`。
`#print axioms parallel_gaussian_capacity_formula_minimal` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free)。
commit `07da6b8` (実装) + `bc72889` (docstring cleanup)。

## ゴール / Approach

### ゴール

`Common2026/Shannon/ParallelGaussianConverse.lean:1093`
`parallelOutput_joint_logDensity_integrable` の唯一の `sorry` を消す。signature は変更しない
(clean な `Integrable` claim + regularity precondition `0 ≤ P` / `hN` / `hp`、load-bearing hyp 無し)。
consumer は同 file 内 2 件 (`:1570`/`:1722`) なので、本体 genuine 化で converse 全体が transitive に genuine 化する。
proof done (0 sorry / 0 residual) を目標とする。

### Approach (solution の shape)

**「1-D AWGN Phase 6 (mixture log-density integrability) の座標積 (`Fin n`) 持ち上げ」が core 戦略。新規数学はゼロ。**

1-D 手本 `outputDistribution_logDensity_integrable` (`AwgnCapacityConverseMaxent.lean:610`, `@audit:ok`) は
出力法 `q = p ∗ 𝒩(0,N)` を `volume.withDensity (outputMixtureDensity)` と書き、mixture density
`f_q(y) = ∫⁻ x, gaussianPDF x N y ∂p` に対し上界 (6a) + Gaussian tail 下界 (6b) → `|log f_q| ≤ c₀ + c₁ y²`
→ 出力 second moment 有限性で `Integrable` を締める。**この 5 段の構造をそのまま座標積に持ち上げる。**

**なぜ wall でなく self-buildable か (1 文)**: 1-D 手本の density 表現 `output_eq_withDensity_mixture`
(`:368`, `@audit:ok`) は **入力 `p` の絶対連続性を一切使わず** (`SFinite p` のみ、`Measure.lintegral_conv`
Tonelli + ノイズ側の `gaussianReal_of_var_ne_zero` 平行移動だけ)、相関入力 `p : Measure (Fin n → ℝ)` でも
そのまま `Measure.pi` ノイズに対して成立する — Tonelli swap が `p` 非依存だから、joint mixture density
`f_Y(z) = ∫⁻ x, ∏ᵢ gaussianPDF (x i)(N i)(z i) ∂p` は `p` がどれだけ相関していても閉形で書ける。
コード現 docstring (`:1059-1092`) の「多変量 mixture density は principled-impossible / true Mathlib gap」は、
「rnDeriv が marginal rnDeriv の積に factor しない」(真) を「mixture density 表現が存在しない」(偽) にすり替えた
classification 誤り (在庫 §一行サマリ / §撤退ラインへの距離)。**`rnDeriv_conv'` (両因子 AC 要求) を直接使うと
`p ≪ volume` が相関入力で偽になり詰まるが、withDensity 手定義ルート (1-D `output_eq_withDensity_mixture`
の n 版) は `p` の AC 不要で回避できる** (在庫 落とし穴①)。

証明の骨格 (在庫 §証明戦略の多変量版、再掲):

```
-- (P1) joint mixture density を閉形に
μY = volume.withDensity (fun z => ∫⁻ x, ∏ᵢ gaussianPDF (x i)(N i)(z i) ∂p)   -- 在庫項目1, Tonelli (p 非依存)
μY.rnDeriv volume =ᵐ[volume] f_Y                                              -- rnDeriv_withDensity (既存)
-- (P2 上界) f_Y(z) ≤ ∏ᵢ (√2πNᵢ)⁻¹                                            -- gaussianPDFReal_le_sup の Finset.prod
-- (P2 集中) p {x | ∀i, |xᵢ|≤Rᵢ} ≥ 1/2                                        -- 座標箱 Chebyshev (Markov 各座標 + union bound)
-- (P3 下界) S 上で ∏ᵢ gaussianPDF ≥ ∏ᵢ Kr(zᵢ) → f_Y(z) ≥ (1/2)∏Kr(zᵢ)        -- 1-D output_logDensity_lower_bound の座標積
-- (P4 合成) |log f_Y(z)| ≤ c₀ + c₁ ∑ᵢ(zᵢ)²
-- (P5 締め) quadratic majorant が μY 上 integrable                            -- 出力 second moment 有限 (既存建材)
```

**依存連鎖**: M0 → Phase 1 → (Phase 2, Phase 3 は Phase 1 完成後に並行着手可) → Phase 4 (2+3 合成) → Phase 5 (締め)。
Phase 3 (★下界) が最重量・最大リスクなので独立 Phase + 独立撤退口に切る。

### ファイル構成

新規 declaration は全て既存 `Common2026/Shannon/ParallelGaussianConverse.lean` 内に追加
(#5 本体・consumer・既存建材が全て同 file。`private` 共有のため別 file 化しない)。
import 追加が要る場合のみ (在庫「着手 skeleton」: `Mathlib.Analysis.LConvolution` /
`Mathlib.MeasureTheory.Integral.Lebesgue.Markov` 等)。`Common2026.lean` への新規 import 行は不要 (既存 file 拡張)。

---

## M0 — 在庫照合 + wall/plan 再裁定の確定 📋

proof-log: no (確認のみ)

**重要 — 着手前に解消すべき分類矛盾**: コード現 docstring (`ParallelGaussianConverse.lean:1059-1092`) は
#5 を `@residual(wall:multivariate-mi)` に再分類し、**独立 honesty audit が「VERIFIED honest / true Mathlib gap」と
記録済**。一方、在庫 (`parallel-gaussian-converse-multivariate-mi-api-inventory.md`) + 後続の proof-pivot 再々裁定は
**「self-buildable (big-but-mechanical ~180-270 行)」** と逆判定している。**この 2 つの記録は矛盾しており、実装着手前に
どちらが正しいか fresh auditor で確定させる** (実装 agent self-申告で wall を撤回しない — CLAUDE.md「Mathlib 壁の誤用」は
両方向に効く)。

- [ ] **wall/plan 再裁定を独立 auditor (`honesty-auditor`) で確定** (実装より前):
  - 渡す材料: (a) 在庫 §カテゴリ2「joint mixture density (★ wall 主張の核心、実は既存)」の compile 証拠
    (`rnDeriv_conv'` が `Fin n → ℝ`/`volume` で `#check` 通過、`/tmp/test_inst3.lean`)、
    (b) 1-D 手本 `output_eq_withDensity_mixture` (`:368`) が **`p` の AC を使わず `SFinite p` のみ** で成立する事実
    (verbatim 確認済: `lintegral_conv` Tonelli + `gaussianReal_of_var_ne_zero` 平行移動のみ、`p` は積分測度として残る)、
    (c) コード現 docstring の wall 根拠「per-coord decomposition が principled-impossible」が実は
    「rnDeriv の factor 不能」と「mixture density の不在」の混同である点、(d) register slug `multivariate-mi`
    (`audit-tags.md:62`) は本来「連続 `mutualInfo_pi_eq_sum` (MI 加法性)」を指し #5 の log-density integrability とは
    semantic に別物 (slug 流用)。
  - **verdict 分岐**:
    - auditor が「self-buildable / wall 主張は overstated」と確定 → docstring の wall 主張を撤回し
      `@residual(wall:multivariate-mi)` → `@residual(plan:parallel-gaussian-converse-5-closure-plan)` に
      reclassify (Phase 1 の最初の step で実施)。本 plan の Phase 1-5 で genuine closure に進む。
    - auditor が「やはり真の wall」と確定 → 本 plan は **撤退** (在庫の self-buildable 判定が誤り)。
      その場合は判断ログに記録し、wall 維持。
  - 注意: コード docstring の既存 audit 記録 (`:1082-1091`) は 1-D 手本の **下界** `output_logDensity_lower_bound`
    が「scalar mixture density に依存」と述べて wall を支持しているが、在庫の反証は「下界の **座標積** が
    `output_logDensity_lower_bound` を各座標に適用するだけ (新規数学なし)」という点。auditor はこの
    **「座標積で済むか / 原理的に factor が要るか」** を判定の中心に据える。
- [ ] **建材の verbatim 再確認** (drift 防止、在庫 §自作が必要な要素 / §建材マップ):
  - 1-D 手本 5 件の signature と `@audit:ok` 状態:
    `outputMixtureDensity` (`:338`)、`output_eq_withDensity_mixture` (`:368`)、
    `outputMixtureDensity_le_sup` (`:420`)、`output_logDensity_lower_bound` (`:440`)、
    `outputMixtureDensity_log_abs_le` (`:557`)、consumer `outputDistribution_logDensity_integrable` (`:610`)。
  - 既存建材 (sorryAx-free 再利用): `pi_withDensity_fin` (`MultivariateDiffEntropy.lean:260`)、
    `parallelGaussianPowerConstraintSet_mem_iff_integrable` (`ParallelGaussian.lean:191`)、
    `parallelOutput_marginal_eq_conv` (`ParallelGaussianConverse.lean:701`)、
    `parallelOutput_centered_secondMoment_eq` (`:1142`)、
    `parallelOutput_absolutelyContinuous_volume` (`:819`)。
  - #5 の最終形 signature (`:1093-1099`) と consumer 2 件 (`:1570`/`:1722`) の呼出形。

---

## Phase 1 — 多変量 mixture density def + withDensity 等式 (在庫項目 1) 📋

proof-log: yes (Fubini opaque-g 回避点・`pi_withDensity_fin` 接続点を記録)

在庫項目 1 (最優先)。1-D `outputMixtureDensity` (`:338`) + `output_eq_withDensity_mixture` (`:368`) の n 版。

### target decl (新規、`ParallelGaussianConverse.lean`)

- [ ] **docstring 訂正 (実装の最初の step)**: M0 で self-buildable と確定したら、#5 docstring
  (`:1050-1092`) の wall 主張 (「no corresponding multivariate mixture-density representation」/
  「principled-impossible」/「true Mathlib gap」) を撤回し、`@residual(wall:multivariate-mi)` を
  `@residual(plan:parallel-gaussian-converse-5-closure-plan)` に書換える。撤回理由を 1-2 行で
  (Tonelli が `p` 非依存 → joint mixture density は閉形で存在、wall 根拠は factor 不能と density 不在の混同)。
- [ ] `parallelOutputMixtureDensity (z : Fin n → ℝ) : ℝ≥0∞ := ∫⁻ x, ∏ i, gaussianPDF (x i) (N i) (z i) ∂p`
  (def、~5 行)。在庫「着手 skeleton」の signature を踏襲。可測性補題 (n 版 `measurable_outputMixtureDensity`、
  `Measurable.lintegral_prod_left'` 系) も併設。
- [ ] `parallelOutput_eq_withDensity_mixture`:
  `outputDistribution p (parallelGaussianChannel …) = volume.withDensity (parallelOutputMixtureDensity N p)`。
  - 帰着先: (a) joint conv 等式 `μY = p ∗ (Measure.pi (fun i => gaussianReal 0 (N i)))`
    (在庫 §カテゴリ1 自作補題、`parallelOutput_marginal_eq_conv` を joint に持ち上げ、~30-50 行)、
    (b) `Measure.lintegral_conv` (Tonelli swap、1-D `:375` の n 版)、(c) `pi_withDensity_fin`
    (`:260`、ノイズ rnDeriv を `∏ gaussianPDF` に)。`p` の AC 不要 (1-D 手本同様)。
  - **落とし穴 (a) Fubini heartbeat**: Tonelli swap で `whnf` が `gaussianReal`/`gaussianPDFReal` を
    unfold して heartbeat timeout。1-D が `set g := fun z => gaussianPDF z.1 N z.2` で opaque 化
    (`:377`)。n 版も **opaque local 必須** (座標積 `∏ᵢ gaussianPDF` を 1 つの opaque measurable function に束ねる)。
- [ ] `parallelOutput_rnDeriv_ae_mixture`:
  `μY.rnDeriv volume =ᵐ[volume] parallelOutputMixtureDensity N p`。
  帰着先: 上の withDensity 等式 + `Measure.rnDeriv_withDensity` (`Lebesgue.lean:590`、1-D `:415` 同型、~5 行)。
- 依存: M0。規模: ~50-80 行。
- **撤退口**: joint conv 等式 (a) が機械的に詰まる場合のみ、その 1 件を `sorry` +
  `@residual(plan:parallel-gaussian-converse-5-closure-plan)`。signature は本来の形のまま、仮説束化しない。

---

## Phase 2 — 上界 (容易) + 座標箱 Chebyshev (在庫項目 3) 📋

proof-log: yes (norm の落とし穴・per-coord moment 接続点を記録)

Phase 3 の下界とは独立に着手可。上界は容易、Chebyshev は下界 (Phase 3) の入力。

### target decl (新規、`ParallelGaussianConverse.lean`)

- [ ] **上界** `parallelOutputMixtureDensity_le_sup`:
  `parallelOutputMixtureDensity N p z ≤ ENNReal.ofReal (∏ i, (Real.sqrt (2π Nᵢ))⁻¹)` (~15-20 行)。
  帰着先: 各座標 `gaussianPDFReal_le_sup` (`AwgnCapacityConverseMaxent.lean:65`、既存) の `Finset.prod`、
  `p` 確率測度で平均が上界を継承 (1-D `:420` の座標積)。
- [ ] **座標箱 Chebyshev** `parallel_concentration_box`:
  `∃ R : Fin n → ℝ, (∀ i, 0 < R i) ∧ p {x | ∀ i, |x i| ≤ R i} ≥ 1/2` (~40-60 行)。
  - 帰着先: 各座標に `meas_ge_le_lintegral_div` (`Markov.lean:104`、generic、`Fin n → ℝ` で compile 済) を
    `ε = ofReal(Rᵢ²)`, `f = ofReal((xᵢ)²)` で適用 → `p {|xᵢ| > Rᵢ} ≤ 1/(2n)` → union bound
    (`measure_iUnion_le` over `Fin n`) で補集合 ≤ 1/2。
  - 入力: per-coord second moment `∫ (xᵢ)² ∂p`
    (`parallelGaussianPowerConstraintSet_mem_iff_integrable` (`:191`) の lintegral 形、既存)。
  - **落とし穴 (b) norm の選択**: `Fin n → ℝ` の `‖·‖` は **sup norm ≠ L2**。1-D の `{|x|≤R}` ball を
    素朴に `{‖x‖≤R}` に持ち上げると `∑ᵢ(xᵢ)²` と直結しない。**集中集合は ball でなく座標箱**
    `S = {x | ∀i, |xᵢ|≤Rᵢ}` に取る (EuclideanSpace / `norm_sq_eq_inner` を経由しない、在庫 §カテゴリ5)。
- 依存: Phase 1 (mixture density def)。規模: ~55-80 行。
- **撤退口**: 座標箱 Chebyshev の union bound が詰まる場合のみ `sorry` +
  `@residual(plan:parallel-gaussian-converse-5-closure-plan)`。

---

## Phase 3 — ★ 下界 (Gaussian tail 座標積、最重量) 📋 ★core / 最大リスク

proof-log: yes (1-D 下界の座標積化で詰まった点・Kr(zᵢ) の構成を記録)

在庫項目 2 の **下界部** = 全 closure で最重量・唯一の hard。1-D `output_logDensity_lower_bound`
(`:440`, `@audit:ok`、`set_option maxHeartbeats 1000000`) の n-座標版。**独立 Phase + 独立撤退口に切る**。

### target decl (新規、`ParallelGaussianConverse.lean`)

- [ ] `parallelOutput_logDensity_lower_bound`:
  `∃ a b : ℝ, 0 ≤ a ∧ ∀ z : Fin n → ℝ, -Real.log ((parallelOutputMixtureDensity N p z).toReal) ≤ a * (∑ i, (z i)²) + b`。
  - 帰着先: Phase 2 の座標箱集中 `p S ≥ 1/2` + `S` 上で各座標 Gaussian tail 下界
    `gaussianPDF (xᵢ)(Nᵢ)(zᵢ) ≥ Kr_i(zᵢ)` の **座標積** `∏ᵢ gaussianPDF ≥ ∏ᵢ Kr_i(zᵢ)`
    → `f_Y(z) ≥ (1/2) ∏ᵢ Kr_i(zᵢ)` → quadratic `-log` 上界。
  - **核心**: 1-D `output_logDensity_lower_bound` (`:440-552`) の内部 Gaussian-tail 下界
    (`hSc_le`/`hS_ge` `:458-494` の集中 + 各点 tail) を **各座標 i に適用して `Finset.prod` で束ねる**。
    factor が「原理的に不能」なのではなく、各座標が独立ノイズ `𝒩(0,Nᵢ)` の積で `∏ gaussianPDF` が
    座標積に分かれる (ノイズ側のみ、入力 `p` は座標箱 `S` の集中で吸収) — ここが wall 主張の反証点。
  - **落とし穴 (b 再掲)**: 集中は座標箱、`∑ᵢ(zᵢ)²` で quadratic を立てる (sup norm を経由しない)。
  - **落とし穴 (a 再掲)**: 座標積 `∏ᵢ gaussianPDF` を扱う lintegral で heartbeat。opaque local + 必要なら
    `set_option maxHeartbeats` (1-D が 1000000 を使用、`:432`)。
- 依存: Phase 1 + Phase 2 (座標箱集中)。規模: ~80-120 行 (在庫見積、最重量)。
- **撤退口 (★ 細分化)**: 着手して下界が想定超過で書けない場合、**上界のみ genuine + 下界を sorry leaf に細分化**:
  - `parallelOutput_logDensity_lower_bound` 自体を `sorry` + `@residual(plan:parallel-gaussian-converse-5-closure-plan)`
    で残し (signature は本来の `∃ a b, …` 形のまま、仮説束化禁止)、Phase 1/2/4/5 の他 piece は genuine に着地させる。
  - これにより #5 本体は transitive にこの 1 sorry のみに依存する状態 (type-check done) で commit 可。
  - 在庫 §撤退ラインへの距離が想定する新規撤退口 (「着手後に下界が想定超過した場合」) に対応。
    `@residual(plan:parallel-joint-lower-envelope)` のような別 slug ではなく、本 plan slug に集約する
    (#5 は単独 leaf、別 plan に切り出すと closure 追跡が分散する)。

---

## Phase 4 — log 絶対値 quadratic 包絡合成 (在庫項目 2 合成部) 📋

proof-log: no (合成のみ)

在庫項目 2 の合成部。1-D `outputMixtureDensity_log_abs_le` (`:557`) の n 版。

### target decl (新規、`ParallelGaussianConverse.lean`)

- [ ] `parallelOutputMixtureDensity_log_abs_le`:
  `∃ c₀ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ z : Fin n → ℝ, |Real.log ((parallelOutputMixtureDensity N p z).toReal)| ≤ c₀ + c₁ * ∑ i, (z i)²`。
  - 帰着先: Phase 2 上界 (log f_Y ≤ const) + Phase 3 下界 (-log f_Y ≤ a∑(zᵢ)²+b) を `abs_le` で合成
    (1-D `:557-590` の `nlinarith` 二項合成と同型、~20 行)。
- 依存: Phase 2 + Phase 3。規模: ~20 行。
- **撤退口**: Phase 3 が sorry leaf 状態なら transitive に依存 (type-check が追跡)。本 decl 自身に新 `@residual` は書かない。

---

## Phase 5 — #5 本体 joint integrable 締め (在庫項目 4) 📋

proof-log: yes (quadratic majorant の μY 上 integrability 接続を記録)

在庫項目 4 = #5 本体。1-D consumer `outputDistribution_logDensity_integrable` (`:610`, `@audit:ok`) の n 版締め。

### target decl (既存 #5 本体、`:1093`)

- [ ] `parallelOutput_joint_logDensity_integrable` の `sorry` (`:1100`) を埋める。
  - 帰着先: (a) `parallelOutput_rnDeriv_ae_mixture` (Phase 1) で被積分関数を mixture density log に書換、
    (b) Phase 4 の quadratic 包絡 `|log f_Y(z)| ≤ c₀ + c₁∑(zᵢ)²`、(c) quadratic majorant が μY 上 integrable:
    出力 second moment `∫ (zᵢ)² ∂μY = ∫(xᵢ)²∂p + Nᵢ`
    (`parallelOutput_centered_secondMoment_eq` (`:1142`) / `parallelOutput_absolutelyContinuous_volume` (`:819`)、
    いずれも既存 sorryAx-free) で有限。`Integrable.mono'` で締め (1-D `:610-` の構造、~20-30 行)。
- 依存: Phase 1 + Phase 4。規模: ~20-30 行。
- **撤退口**: 上流 Phase に sorry が残れば transitive に伝播。本体に新 `@residual` は書かない
  (上流 source で管理、audit-tags 規約)。**禁止**: 本体の核を `*Hypothesis` predicate に再 bundle して
  `sorry` を消す (tier-5 逆戻り)。

---

## 落とし穴サマリ (実装 brief に渡す)

在庫 §自作が必要な要素 / 落とし穴①②③ の集約。

| # | 落とし穴 | 対処 | 該当 Phase |
|---|---|---|---|
| (a) | Fubini swap / 座標積 lintegral で `whnf` が `gaussianReal`/`gaussianPDFReal` を unfold → heartbeat timeout | `set g := …` で opaque local 化 (1-D `:377`/`:432` 参照)、必要なら `set_option maxHeartbeats 1000000` | 1, 3 |
| (b) | `Fin n → ℝ` の `‖·‖` は sup norm ≠ L2 → ball で `∑(xᵢ)²` と直結しない | 集中集合を **座標箱** `{x | ∀i, |xᵢ|≤Rᵢ}` に取る (EuclideanSpace 不経由)、quadratic は `∑ᵢ(zᵢ)²` で | 2, 3 |
| (c) | `p ≪ volume` は相関入力で不成立 (Dirac at 0 ∈ constraint set) → `rnDeriv_conv'` (両因子 AC) 直接使用で詰まる | withDensity 手定義ルート (1-D `output_eq_withDensity_mixture` の n 版) を使う、`p` の AC を要求しない | 1 |

---

## 撤退ライン

在庫の判定: **full closure 可能、撤退ライン発動 NO が基本線** (M0 で self-buildable 確定が前提)。
ただし「★下界が想定超過」リスクに対する段階的細分化を明示する。「全部 genuine か、さもなくば honest sorry」で
**load-bearing hyp 再 bundle は禁止**。

| # | 縮退案 | 残す `sorry` の `@residual` | 残量 |
|---|---|---|---|
| (a) | M0 で auditor が「やはり真の wall」と確定 ⇒ 本 plan 撤退、wall 維持 | `@residual(wall:multivariate-mi)` (現状維持) | 1 件。docstring 撤回せず。判断ログに記録 |
| (b) | Phase 3 ★下界が着手後に想定超過で書けない ⇒ 上界 + Chebyshev は genuine、下界のみ sorry leaf | `@residual(plan:parallel-gaussian-converse-5-closure-plan)` (Phase 3 の 1 件) | 1 件。#5 本体は transitive にこの 1 件へ依存 |
| (c) | Phase 1 joint conv 等式が機械的に詰まる ⇒ その 1 件のみ sorry | `@residual(plan:parallel-gaussian-converse-5-closure-plan)` | 1 件。precondition でなく density 表現の橋なので本 plan 内 closure 待ち |

**禁止**: #5 本体 / mixture 包絡の核を `*Hypothesis` predicate に再 bundle して `sorry` を消す (tier-5)。
詰まったら必ず `sorry` + `@residual(plan:parallel-gaussian-converse-5-closure-plan)` の tier-2 で残す。
別 slug (`parallel-joint-lower-envelope` 等) に切り出さず、本 plan slug に集約 (#5 は単独 leaf)。

---

## `@residual` 分類 / reclassify 方針

- **現状** (本 plan 着手前): #5 (`:1092`) は `@residual(wall:multivariate-mi)`。コード docstring は
  wall を「VERIFIED honest」と記録するが、在庫 + 後続 proof-pivot は self-buildable と逆判定 (M0 で確定)。
- **M0 で self-buildable 確定後**: docstring の wall 主張を撤回し
  `@residual(wall:multivariate-mi)` → `@residual(plan:parallel-gaussian-converse-5-closure-plan)` に reclassify
  (Phase 1 最初の step)。`multivariate-mi` register entry (`audit-tags.md:62`) は本来「連続 MI 加法性」を指すので、
  #5 の流用解消 = register からの誤 consumer 除去。
- **着手中** (Phase 3 が sorry leaf のまま等): self-build 残課題は
  `@residual(plan:parallel-gaussian-converse-5-closure-plan)` のまま。
- **着地後** (全 Phase genuine、0 sorry): タグを `@audit:ok` に書換 (audit-tags.md「解除」)。
  親計画 `parallel-gaussian-converse-closure-plan.md` の進捗 #5 を ✅ に更新。
- reclassify / 解除は **Phase 6 独立監査の verdict 確定後**に行う (実装 self-申告でなく fresh auditor が classification verify)。

---

## Phase 6 — 独立 honesty 監査 + 解除 📋

proof-log: no

M0 の wall/plan 再裁定 + Phase 1-5 で新規 `sorry`/`@residual` 導入 or reclassify or 完全解除があるため、
CLAUDE.md「Independent honesty audit」に従い orchestrator が `honesty-auditor` を起動。

- [ ] 対象: 新規 mixture density 系 declaration 全件 + #5 本体 `parallelOutput_joint_logDensity_integrable`。
- [ ] 監査スコープ (audit-tags.md):
  - signature honesty: 各 mixture 補題が結論型 ≡ 仮説型 (`:= h` 循環) になっていないか、`*Hypothesis` predicate に
    核を bundling していないか、座標箱集中 / 下界が退化定義悪用 (vacuous) していないか。
  - `@residual` classification: 残 sorry が `plan:parallel-gaussian-converse-5-closure-plan` (self-build) か
    `wall:multivariate-mi` (真の gap) か正しいか。完全 genuine 化なら `@audit:ok` 付与可か。
  - regularity (`0 ≤ P` / `hN` / `hp` / `SFinite p` / `IsProbabilityMeasure p`) が precondition として
    genuine 消費されているか (load-bearing 再 bundle がないか)。
- [ ] verdict 全 OK ⇒ 解除 (`@audit:ok`) or reclassify 確定 + 親計画進捗更新 + handoff 明記。
  DEFECT ⇒ 当該 declaration を sorry-based に戻す。

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **本 plan の起点 (2026-05-29)**: 親計画 `parallel-gaussian-converse-closure-plan.md` の唯一の残 residual
   #5 `parallelOutput_joint_logDensity_integrable` を専用 closure する sub-plan を起草。在庫
   `parallel-gaussian-converse-multivariate-mi-api-inventory.md` + 後続 proof-pivot 再々裁定が
   #5 を **self-buildable (1-D Phase 6 の座標積持ち上げ、~180-270 行、big-but-mechanical)** と判定。
   1-D 手本 `output_eq_withDensity_mixture` (`AwgnCapacityConverseMaxent.lean:368`, `@audit:ok`) が
   **入力 `p` の AC を使わず `SFinite p` のみで成立** (Tonelli が `p` 非依存) という verbatim 確認が反証の核。
2. **wall/plan 矛盾を M0 で先決 (2026-05-29)**: コード現 docstring (`:1059-1092`) は #5 を
   `wall:multivariate-mi` に再分類し独立 audit が「VERIFIED honest / true Mathlib gap」と記録済。
   在庫 + 後続 proof-pivot の self-buildable 判定と **矛盾**。実装 self-申告で wall を撤回するのは
   「Mathlib 壁の誤用」の逆方向 defect になりうるため、**M0 で fresh `honesty-auditor` に再裁定させ確定してから**
   docstring 撤回 / reclassify に進む設計とした。判定の中心は「1-D 下界の **座標積** で済むか / 原理的に
   per-coord factor が要るか」。auditor が「やはり wall」と確定したら本 plan は撤退 (撤退ライン (a))。
3. **★下界を独立 Phase + 細分化撤退口に (2026-05-29)**: 在庫が項目 2 下界 (1-D `output_logDensity_lower_bound`
   の座標積、~80-120 行) を最重量と名指し。これを Phase 3 として独立化し、想定超過時は「上界 + Chebyshev は
   genuine、下界のみ sorry leaf」に細分化する撤退口 (撤退ライン (b)) を明示。別 slug に切らず本 plan slug に集約。
