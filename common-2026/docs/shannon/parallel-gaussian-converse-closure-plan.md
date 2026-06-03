# Parallel Gaussian: ② converse genuine closure サブ計画

> **Parent**: [`parallel-gaussian-headline-honest-restructure-plan.md`](parallel-gaussian-headline-honest-restructure-plan.md)
> — その restructure で `isParallelGaussianPerCoordRegularity_of_pieces` の `bddAbove`/`max_ent` 2 field が
> tier-2 `sorry` + `@residual(wall:multivariate-mi)` に落とされた。本 plan はその 2 件を **genuine 着地**させる。
> **Inventory (SoT)**: [`parallel-gaussian-converse-multivariate-mi-inventory.md`](parallel-gaussian-converse-multivariate-mi-inventory.md)
> — 完全な部品在庫・hyp 分類表・規模見積を保持。本 plan は在庫の推奨着手順序を Phase 化したもの。

<!--
記法: 状態絵文字 📋/🚧/✅/🔄、取り消し線で廃止 Phase、判断ログ append-only。
本 plan は docs-only。Lean 実装は lean-implementer に dispatch。
plan filename stem = `parallel-gaussian-converse-closure-plan` →
着地時に @residual(wall:multivariate-mi) を @residual(plan:parallel-gaussian-converse-closure-plan)
へ reclassify する基準 slug (§reclassify 参照)。
-->

## 進捗

- [ ] M0 在庫確認 + `CountableOrCountablyGenerated (Fin n → ℝ)` instance 確定 📋
- [ ] Phase 1 — correlated-input output regularity 6 件 genuine 供給 (在庫 #3) 📋
- [ ] Phase 2 — `h_decomp` lift: channel↔RV MI decomp の `Fin n → ℝ` 版 (在庫 #1) 📋
- [ ] Phase 3 — per-coord max-entropy converse split (在庫 #2) 📋
- [ ] Phase 4 — `max_ent` field 組立 (constructor `:127` の sorry を埋める) 📋
- [ ] Phase 5 — `bddAbove` field (constructor `:120` の sorry を埋める、在庫 #4) 📋
- [ ] Phase 6 — 独立 honesty 監査 + `@residual` reclassify 📋

## ゴール / Approach

### ゴール

`InformationTheory/Shannon/ParallelGaussianPerCoordRegularity.lean` の constructor
`isParallelGaussianPerCoordRegularity_of_pieces` 内、2 件の `sorry` を消す:

- `:120` — `bddAbove` field: `BddAbove (miImage P N h_meas h_parallel_meas)`
- `:127` — `max_ent` field: 任意 feasible `p ∈ parallelGaussianPowerConstraintSet P` に対する
  per-coord max-entropy converse split (`∃ P', … ≤ ∑ᵢ (1/2)log(1+P'ᵢ/Nᵢ)`)

両 field は **相関入力 (correlated) 上の converse** であり、achiever 側 product-input closure では閉じない。
proof done (0 sorry / 0 residual) を目標とする。

### Approach (solution の shape)

**「1-D AWGN converse の `Fin n` lift」が core 戦略。新規数学はゼロ。**

在庫の判定: `wall:multivariate-mi` は誤分類気味で、これは "hard wall" でなく "big (規模 ~285-430 行)"。
InformationTheory が必要部品を全て genuine 保有している:

1. **1-D converse 完成形** `awgn_per_input_mi_le_log` (`AwgnCapacityConverseMaxent.lean:742`, `@audit:ok`)
   — decomp + max-ent + fibre 定数 + Var(Y)≤P+N + log-algebra を 1 theorem に統合済。これを各 coord で再演する。
2. **n-変量 output-entropy subadditivity** `jointDifferentialEntropyPi_le_sum`
   (`MultivariateDiffEntropy.lean`, genuine) — `h(Yⁿ) ≤ ∑ᵢ h(Yᵢ)`。**既に genuine 化済が core 前進点**。
3. **組立 wrapper** `parallelGaussian_max_ent_le_of_subadditivity`
   (`ParallelGaussianPerCoord.lean:293`) — subadditivity を呼んで `h_decomp` + `h_perCoord` + 6 regularity
   を `linarith` で組む形が既に存在。残 load-bearing hyp = `h_decomp` (核心1) + `h_perCoord` (核心2) のみ。
   本 plan は **この 2 つの hyp に honest hypothesis でなく実値を供給**して wrapper を呼ぶ。
4. **generic 核** `rnDeriv_compProd_fibre` (`{α β} generic`) / `integral_log_rnDeriv_self_eq_neg`
   (`{α} generic`) — decomp lift の依存核が既に多変量で使える。

証明の骨格 (在庫 §冒頭の pseudo-Lean、再掲):

```
I(p; parallelChan).toReal
  = jointDiffEntropyPi(μ_Y) − ∫ jointDiffEntropyPi(W x) ∂p   -- (★1) Phase 2 (decomp lift)
  ≤ ∑ᵢ h(Yᵢ) − ∫ ... ∂p                                       -- jointDifferentialEntropyPi_le_sum (既存 genuine)
  ≤ ∑ᵢ [(1/2)log(2πe·Var(Yᵢ)) − (1/2)log(2πe·Nᵢ)]            -- Phase 3 (per-coord Gaussian max-ent)
  ≤ ∑ᵢ (1/2)log(1 + P'ᵢ/Nᵢ)                                   -- log-algebra (1-D template 同一)
```

**依存連鎖**: M0 → Phase 1 (regularity) → Phase 2 (decomp) は順序固定。Phase 3 は Phase 1 と独立に着手可。
Phase 4 (組立) は Phase 2+3+1 完成後。Phase 5 (`bddAbove`) は Phase 3 完成後 (RHS が p-非依存定数上界)。

**段階的縮退 (honest 撤退口)**: 各 Phase は独立 `lake env lean` 検証可。genuine に進めない箇所は
`sorry` + `@residual` のまま残し、**load-bearing hyp 再 bundle は禁止**。最悪縮退案 (§撤退ライン) は
「decomp lift だけ wall 維持、他 3 piece は genuine 着地」。

### ファイル構成

新規 `InformationTheory/Shannon/ParallelGaussianConverse.lean` を起こし、Phase 1-3 の補題群を置く。
constructor (`ParallelGaussianPerCoordRegularity.lean`) は Phase 4/5 でその補題を呼んで sorry を埋める。
import は在庫「着手 skeleton」(§着手 skeleton) 記載のものを踏襲 (ContChannelMIDecomp / MultivariateDiffEntropy
/ DifferentialEntropy / AwgnCapacityConverseMaxent / Constructions.Pi)。完了時 `InformationTheory.lean` に import 1 行追加。

---

## M0 — 在庫確認 + instance 確定 📋

proof-log: no (確認のみ)

在庫が「1-turn リスク」と名指しした **唯一の構造リスク**を先に潰す。

- [ ] **`CountableOrCountablyGenerated (Fin n → ℝ)` instance の有無を verbatim 確認**。
  `rnDeriv_compProd_fibre` (`ContChannelMIDecomp.lean:144`) が
  `[MeasurableSpace.CountableOrCountablyGenerated α β]` を要求。`α = β = (Fin n → ℝ)` で resolve するか。
  - **既知の事実** (本 plan 策定時の loogle 確認、2026-05-29):
    - `MeasurableSpace.CountableOrCountablyGenerated (Fin n → ℝ) (Fin n → ℝ)` という named instance は
      loogle で 0 件 (直接 hit なし)。
    - ただし Mathlib に `instCountableOrCountablyGeneratedOfCountablyGenerated` +
      `instCountableOrCountablyGeneratedProd` + `MeasurableSpace.CountablyGenerated` の Pi/有限積 instance が
      存在。`ℝ` は `CountablyGenerated`、`Fin n` は `Countable` なので
      `Fin n → ℝ` (= 有限 index 上の Pi) は `CountablyGenerated` instance を継承する見込み。
  - **確認手順**: skeleton file に
    `example {n : ℕ} : MeasurableSpace.CountableOrCountablyGenerated (Fin n → ℝ) (Fin n → ℝ) := by infer_instance`
    を 1 行書いて `lake env lean` を回す。silent なら instance あり (Phase 2 続行)。
    fail なら `Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated` を import して再試行、
    それでも fail なら `MeasurableSpace.CountablyGenerated (Fin n → ℝ)` を別途立てて
    `CountableOrCountablyGenerated.mk` 経由で derive。
  - **撤退口** (M0 で instance が立たない場合のみ): Phase 2 decomp lift の当該 1 件を
    `sorry` + `@residual(wall:multivariate-mi)` で staged 維持し、他 Phase (1/3/4/5) を genuine 着地させる。
    instance 不在は新規数学でなく Mathlib API gap なので wall 維持が honest。
- [ ] **現 signature の verbatim 再確認** (drift 防止):
  - constructor field 型: `ParallelGaussianPerCoordRegularity.lean:115/117` の `bddAbove`/`max_ent` `?_` slot。
  - wrapper `parallelGaussian_max_ent_le_of_subadditivity` の hyp 表 (`ParallelGaussianPerCoord.lean:293-312`)。
  - 1-D 手本 `awgn_per_input_mi_le_log` の STEP 構造 (`AwgnCapacityConverseMaxent.lean:742-829`)。

---

## Phase 1 — correlated-input output regularity (在庫 #3) 📋

proof-log: yes (最大 plumbing、Phase 6 integrability の模倣点を記録)

在庫 §A の 6 件 regularity hyp を、相関入力 `p` の出力法
`μY := outputDistribution p (parallelGaussianChannel N …)` で genuine に供給する。
achiever の product factorization は使えない (在庫 §D)。これが無いと Phase 2 decomp が呼べないので先行。

### target decl (新規、`ParallelGaussianConverse.lean`)

各 regularity を個別補題で立てる (在庫 §D の規模見積に対応):

- [ ] `hμ_ac : μY ≪ (volume : Measure (Fin n → ℝ))` — 各 fibre `Measure.pi (gaussianReal (xᵢ)(Nᵢ))` は
  Gaussian 平滑化 ⇒ full-support ⇒ AC。`Measure.pi` AC + 1-D `Measure.conv_absolutelyContinuous`
  (`AwgnCapacityConverseMaxent.lean:763` で使用) の n-変量版。規模 ~20 行。
- [ ] `h_marg_ac : ∀ i, (μY.map (· i)) ≪ volume` — marginal も Gaussian 平滑化。push-forward + 1-D conv AC。~15 行。
- [ ] `h_joint_ac : μY ≪ Measure.pi (fun i => μY.map (· i))` — **要注意点**: correlated 入力で
  joint ≠ ∏marginal だが、両者が volume と相互 AC なら推移的に `≪` が立つ見込み (在庫 §D)。
  Gaussian 平滑化 full-support が鍵。~25 行。**genuine に立たない場合は §撤退ライン (a)**。
- [ ] `h_int_marg` / `h_int_joint` (log-density integrability) — **最大単項**。1-D は
  `outputDistribution_logDensity_integrable[_joint]` (`AwgnCapacityConverseMaxent.lean:739/791/824` Phase 6,
  ~75 行で genuine 完成) の構造模倣。n-変量で ~60-100 行。
- 依存: M0 の instance (joint AC で compProd 系を触る場合)。
- 規模合計: 在庫 §D で ~120-160 行。
- **撤退ライン**: 各 regularity が genuine に立たない場合、当該 1 件のみ `sorry` + `@residual` で残し
  (`@residual(plan:parallel-gaussian-converse-closure-plan)`)、他は genuine。precondition なので
  load-bearing でない (hyp として wrapper に残すのは OK だが、本 plan の目標は実値供給)。

---

## Phase 2 — `h_decomp` lift (channel↔RV MI decomp、在庫 #1) 📋 ★core

proof-log: yes (Mathlib API hardwire の lift 困難度を記録)

在庫 §B = 残 wall の本体。1-D decomp `mutualInfoOfChannel_toReal_eq_diffEntropy_sub`
(`ContChannelMIDecomp.lean:276`) が `Measure ℝ` / `Channel ℝ ℝ` / `differentialEntropy` (1-D) に
**ハードワイヤ**されており、generic 再インスタンス化では lift 不可。**新規 decl の自作**になる。

### target decl (新規、`ParallelGaussianConverse.lean`)

- [ ] `parallel_mutualInfoOfChannel_toReal_eq_diffEntropyPi_sub` — 在庫「着手 skeleton」記載の
  signature (verbatim):
  ```
  (p : Measure (Fin n → ℝ)) [IsProbabilityMeasure p]
  (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
      = jointDifferentialEntropyPi (outputDistribution p (parallelGaussianChannel …))
        - ∫ x, jointDifferentialEntropyPi ((parallelGaussianChannel …) x) ∂p
  ```
- [ ] 依存部品の lift (在庫 §B 表):
  - `rnDeriv_compProd_fibre` — fully generic、M0 instance で `α=β=(Fin n→ℝ)` に適用 (lift 不要)。
  - `integral_log_rnDeriv_self_eq_neg` (`MultivariateDiffEntropy.lean:86`) — generic `{α}`、再利用 (lift 不要)。
  - `log_rnDeriv_split` (`ContChannelMIDecomp.lean:171`, ℝ-specific) → `Measure (Fin n → ℝ)` 一般化 ~15 行。
  - `llr_compProd_prod_split` (`:206`, ℝ-specific) → `Fin n → ℝ` 版自作 ~30 行。
  - `integral_log_rnDeriv_eq_neg_diffEntropy` (`:85`) → `jointDifferentialEntropyPi` 版を新規 ~10 行
    (generic 核 `integral_log_rnDeriv_self_eq_neg` 再利用)。
  - body 全体 → `Fin n → ℝ` 版 theorem を新規記述 ~40 行。
- [ ] fibre 側 `∫ x, jointDifferentialEntropyPi (W x) ∂p`: parallel fibre
  `W x = Measure.pi (gaussianReal (xᵢ)(Nᵢ))` は積測度なので
  `jointDifferentialEntropyPi (Measure.pi …) = ∑ᵢ differentialEntropy (gaussianReal …)` (積→和) の補題が要る
  (Phase 3 per-coord max-ent で消費)。
- 依存: M0 (instance) + Phase 1 (regularity を decomp body で消費)。
- 規模: 在庫 §E で ~80-120 行。
- **撤退ライン**: M0 で instance が立たない / lift が機械的に通らない場合のみ、この 1 件を
  `sorry` + `@residual(wall:multivariate-mi)` で staged 維持。これが在庫の認めた唯一の wall 残量候補。
  他 Phase は genuine 着地可。

---

## Phase 3 — per-coord max-entropy converse split (在庫 #2) 📋

proof-log: yes (variance allocation `P'ᵢ` の構成を記録)

在庫 §C。各 marginal `μY.map (· i)` (= `Measure ℝ`) に Gaussian max-entropy を適用し、
`Fin n` 全 coord を `Finset.sum_le_sum` で束ねる。Phase 1 とは独立に着手可。

### target decl (新規、`ParallelGaussianConverse.lean`)

- [ ] `parallel_per_input_mi_le_sum` — 在庫「着手 skeleton」記載の signature (verbatim):
  ```
  (p : Measure (Fin n → ℝ)) [IsProbabilityMeasure p]
  (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    ∃ P' : Fin n → ℝ, (∀ i, 0 ≤ P' i) ∧ (∑ i, P' i ≤ P) ∧
      (mutualInfoOfChannel p (parallelGaussianChannel …)).toReal
        ≤ ∑ i, (1/2) * Real.log (1 + P' i / (N i : ℝ))
  ```
  (これが `max_ent` field の型と verbatim 一致 ⇒ Phase 4 で field に直接代入できる)。
- [ ] 部品 (在庫 §C 表):
  - `differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:520`, `@audit:ok`) — 各 marginal
    max-ent 上界。**hyp に `hv : v ≠ 0` を要求** ⇒ variance allocation で `vᵢ ≠ 0` を保証する必要 (§退化ガード)。
  - `differentialEntropy_gaussianReal` (`DifferentialEntropy.lean`, `:806` で参照) — fibre
    `h(Zᵢ) = (1/2)log(2πe·Nᵢ)` 定数。
  - 1-D 手本 `awgn_per_input_mi_le_log` STEP 1-3 (`AwgnCapacityConverseMaxent.lean:792-829`) を sum 化。
- [ ] **variance allocation `P'ᵢ := Var(Yᵢ) − Nᵢ`** の構成:
  - 相関でも total 2nd moment は sum で立つ (`∑Var(Yᵢ) ≤ P + ∑Nᵢ` ⇒ `∑P'ᵢ ≤ P`)。
  - `0 ≤ P'ᵢ` を示すには `Var(Yᵢ) = Var(Xᵢ) + Nᵢ ≥ Nᵢ` (独立ノイズ加法)。
  - Phase 1 の moment bound (`parallelGaussianPowerConstraintSet_mem_iff_integrable`,
    `ParallelGaussian.lean:191`, `@audit:ok`) を入力として使う。
- 依存: Phase 1 (marginal AC + integrability)、M0 不要。
- 規模: 在庫 §E で ~50-80 行。
- **撤退ライン**: variance allocation の `0 ≤ P'ᵢ` / `∑ P'ᵢ ≤ P` が機械的に詰まる場合のみ
  `sorry` + `@residual(plan:parallel-gaussian-converse-closure-plan)`。max-ent 補題自体は既存 genuine なので
  wall でなく組立残課題。

---

## Phase 4 — `max_ent` field 組立 📋

proof-log: no (wrapper 呼び出しのみ)

constructor `isParallelGaussianPerCoordRegularity_of_pieces` (`:125-127`) の `max_ent` field の sorry を埋める。

- [ ] Phase 3 の `parallel_per_input_mi_le_sum` が `max_ent` field 型と verbatim 一致するので、
  `intro p hp` 後に直接 `exact parallel_per_input_mi_le_sum p hp` (または in-body で
  `parallelGaussian_max_ent_le_of_subadditivity` を Phase 2 `h_decomp` + Phase 3 `h_perCoord`
  + Phase 1 regularity で呼ぶ経路)。
- [ ] **2 経路の選択** (M0/Phase 完成度次第):
  - 経路 A (推奨): Phase 3 が field 型を直接満たす形なら `exact` 一発。
  - 経路 B: wrapper `parallelGaussian_max_ent_le_of_subadditivity` (`PerCoord.lean:293`) を経由し、
    `h_decomp` = Phase 2、`h_perCoord` = Phase 3 の per-coord 部、6 regularity = Phase 1 を供給。
- 依存: Phase 1 + 2 + 3。
- 規模: 在庫 §E で ~20-40 行。
- **撤退ライン**: 上流 Phase に残 `sorry` があれば transitive に伝播 (type-check が追跡)、
  field 自体に新 `@residual` は書かない (上流 source で管理、audit-tags 規約)。

---

## Phase 5 — `bddAbove` field (在庫 #4) 📋

proof-log: no

constructor (`:118-120`) の `bddAbove` field の sorry を埋める。

- [ ] Phase 3 完成後、`miImage P N …` の各元 `(mutualInfoOfChannel p …).toReal` は
  `∑ᵢ (1/2)log(1+P'ᵢ/Nᵢ) ≤ ∑ᵢ (1/2)log(1+P/Nᵢ)` で **p-非依存の定数上界**を持つ
  (`P'ᵢ ≤ ∑P'ⱼ ≤ P` から各項単調)。
- [ ] `BddAbove` は「上界が存在」を示すだけなので、定数上界を witness にして `⟨const, …⟩`。
  `miImage` の定義 (`ParallelGaussian.lean` 周辺、要 verbatim 確認) に合わせて `Set.mem` 展開。
- 依存: Phase 3。
- 規模: 在庫 §E で ~15-30 行。
- **撤退ライン**: Phase 3 が staged の場合のみ transitive 残。それ以外は genuine。

---

## 【最重要 — 退化ガード】

CLAUDE.md「退化定義の悪用」(tier-5) を Phase 3 / 4 / 5 で踏まないためのガード。在庫 §F の verbatim 確認に基づく。

### 前提の非対称性 (要注意)

- headline `parallel_gaussian_capacity_formula_minimal` (`ParallelGaussianPerCoordRegularity.lean:163`)
  は `hP : 0 < P` を要求。
- **constructor `isParallelGaussianPerCoordRegularity_of_pieces` (`:108`) は `P : ℝ` 無制約**
  (`hP` を取らない)。Phase 4/5 で field を埋めるのは constructor 側なので、**`P < 0` / `P = 0` でも
  converse 不等式を genuine に示す**必要がある。

### genuine に処理すべき退化 case (exfalso 悪用しない)

在庫 §F の verbatim 確認結果:

- **`P < 0`**: `parallelGaussianPowerConstraintSet P` の制約は
  `∑ᵢ ∫⁻ ofReal((xᵢ)²) ≤ ENNReal.ofReal P` (`ParallelGaussian.lean:175-177`、verbatim 確認済)。
  `P < 0` ⇒ `ENNReal.ofReal P = 0` ⇒ 各座標 2nd moment `= 0` ⇒ 入力は Dirac at 0 (vacuous でなく退化)。
  - **NG (tier-5 退化悪用)**: 「`P < 0` なら set が空/自明だから exfalso」。set は空でなく Dirac を含む。
  - **OK (genuine)**: 入力 Dirac ⇒ `Var(Xᵢ) = 0` ⇒ `P'ᵢ := Var(Yᵢ) − Nᵢ = 0` ⇒
    RHS `∑ᵢ (1/2)log(1+0/Nᵢ) = ∑ᵢ (1/2)log 1 = 0`。MI は入力決定論で `I = 0 ≤ 0`。**両辺 0 で genuine 成立**。
    ただし `∑P'ᵢ ≤ P` (`= 0 ≤ P` だが `P < 0`) は **成立しない** ⇒ allocation で `P'ᵢ ≥ 0` を確保しつつ
    `∑P'ᵢ ≤ max 0 P` のような形か、Dirac case を `Var(Yᵢ) = Nᵢ` で `P'ᵢ = 0` とし `∑ 0 = 0 ≤ P` が
    `P < 0` で破れる点を再検討。**Phase 3 で `∑P'ᵢ ≤ P` の成立条件を verbatim 確認** (set membership が
    実際に供給する moment bound `∑∫(xᵢ)² ≤ P` を Bochner 形 `parallelGaussianPowerConstraintSet_mem_iff_integrable`
    で取り出し、`∑P'ᵢ = ∑(Var(Yᵢ)−Nᵢ) = ∑Var(Xᵢ) ≤ ∑∫(xᵢ)² ≤ P` で立てる。`P < 0` なら set が Dirac only ⇒
    `∑Var(Xᵢ) = 0 ≤ P` は `P < 0` で破れる ⇒ **この場合は set membership 自体が `0 ≤ P` を含意** ⇒
    `P < 0` で set 空ではないが moment bound `0 ≤ ofReal P = 0` は `P<0` でも `ENNReal.ofReal P = 0` なので
    成立、Bochner 側 `∑∫(xᵢ)² ≤ P` は `P<0` で偽になりうる)。
  - **判定**: `P < 0` の退化は `parallelGaussianPowerConstraintSet_mem_iff_integrable` の `hP : 0 ≤ P` 要求
    (`ParallelGaussian.lean:192`、verbatim 確認済) と整合させる。membership から moment bound を引く補題が
    `0 ≤ P` を要求するなら、`P < 0` case は **membership と Bochner bridge の整合性で genuine に処理**
    (exfalso でなく、bridge が要求する `0 ≤ P` を case 分けして `P < 0` では Bochner bound を使わず
    lintegral=0 から直接 Dirac を導く)。**Phase 3 着手時に実 set 定義から verbatim で再確認**。
- **`P = 0`**: 上と同様、入力 Dirac、RHS = 0、`I = 0`。両辺 0 で genuine。`∑P'ᵢ = 0 ≤ 0` も成立。退化悪用なし。
- **`N i = 0` の座標**: 発生しない。constructor も `hN : ∀ i, (N i : ℝ) ≠ 0` を取る (`:109`、verbatim 確認済)。
  fibre Dirac (`gaussianReal μ 0 = Measure.dirac μ`, Mathlib `gaussianReal_zero_var`) は precondition `hN` で排除。
  max-ent 補題の `hv : v ≠ 0` とも整合 (在庫 §F)。
- **相関で marginal Dirac の座標**: 出力 `Yᵢ = Xᵢ + Zᵢ` は `Zᵢ ∼ 𝒩(0,Nᵢ)` (`Nᵢ ≠ 0`) との conv ⇒
  full-support Gaussian-smoothed ⇒ AC genuine。出力側で退化しない (在庫 §F)。

### ガード要約 (実装 brief に渡す 1 行)

「`P ≤ 0` の退化 case は **両辺 0 / 入力 Dirac で genuine に converse を示す**。
`P < 0` で `constraintSet` が trivially 成立する/空になることを突いた `exfalso` / vacuous truth は
**書かない** (tier-5 退化定義悪用)。set 定義 (`ParallelGaussian.lean:175`) と
`_mem_iff_integrable` の `0 ≤ P` 要求 (`:192`) を verbatim 照合してから case 分け。」

---

## 撤退ライン

在庫の判定: **full closure 可能、撤退ライン発動 NO** が基本線。ただし 1 turn リスク (M0 instance) に対する
段階的縮退案を明示する。「全部 genuine か、さもなくば honest sorry」で **load-bearing hyp 再 bundle は禁止**。

| # | 縮退案 | 残す `sorry` の `@residual` | 残量 |
|---|---|---|---|
| (a) | M0 で `CountableOrCountablyGenerated (Fin n → ℝ)` が立たない ⇒ Phase 2 decomp lift のみ wall 維持 | `@residual(wall:multivariate-mi)` (Phase 2 の 1 件) | 1 件。Phase 1/3/4/5 は genuine、`max_ent`/`bddAbove` は transitive にこの 1 件へ依存 |
| (b) | Phase 1 `h_joint_ac` (correlated joint ≪ ∏marginal) が genuine に立たない | `@residual(plan:parallel-gaussian-converse-closure-plan)` (該当 1 件) | precondition なので wall でない。本 plan 内 closure 待ち |
| (c) | Phase 3 variance allocation が機械的に詰まる | `@residual(plan:parallel-gaussian-converse-closure-plan)` | 組立残課題。max-ent 補題は既存 genuine |

**禁止**: `bddAbove`/`max_ent` field の核を `*Hypothesis` predicate に再 bundle して `sorry` を消す
(これは restructure 前の tier-5 状態への逆戻り)。詰まったら必ず `sorry` + `@residual` の tier-2 で残す。

---

## `@residual` 分類 / reclassify 方針

在庫の判定「`wall:multivariate-mi` は誤分類気味 (self-buildable)」を受けた reclassify 規約:

- **現状** (本 plan 着手前): constructor `:120`/`:127` は `@residual(wall:multivariate-mi)`。
- **着手中** (Phase 2-5 が一部 sorry のまま): self-buildable と確定した残課題は
  `@residual(plan:parallel-gaussian-converse-closure-plan)` に reclassify する
  (= 本 plan で closure 予定の self-build 課題)。**例外**: M0 instance が立たず Phase 2 を staged 維持する
  場合のみ、その 1 件は `@residual(wall:multivariate-mi)` 維持 (真の Mathlib API gap として honest)。
- **着地後** (全 Phase genuine、0 sorry): タグを `@audit:ok` に書き換え (audit-tags.md「解除」)。
  `wall:multivariate-mi` register entry (`audit-tags.md:62`) は他 consumer (もしあれば) が無くなった時点で
  closure 記録を追記 (AWGN 系の CLOSED 注記と同形式)。
- reclassify は **Phase 6 独立監査の verdict 確定後**に行う (実装 agent self-申告でなく fresh auditor が
  classification を verify)。

---

## Phase 6 — 独立 honesty 監査 📋

proof-log: no

新規 `sorry` + `@residual` 導入 / 既存 `wall:multivariate-mi` の reclassify が session 内にあるため、
CLAUDE.md「Independent honesty audit」に従い orchestrator が `honesty-auditor` を 1 件起動。

- [ ] 対象: 新規 `ParallelGaussianConverse.lean` の全 declaration + constructor
  `isParallelGaussianPerCoordRegularity_of_pieces` の `bddAbove`/`max_ent` field。
- [ ] 監査スコープ (audit-tags.md):
  - signature honesty: `parallel_per_input_mi_le_sum` / `parallel_mutualInfoOfChannel_…` が結論型 ≡ 仮説型に
    なっていないか、退化定義悪用 (P<0 exfalso) していないか (§退化ガード)。
  - `@residual` classification: 残 sorry が `wall:multivariate-mi` (真の API gap) か
    `plan:parallel-gaussian-converse-closure-plan` (self-build 残課題) か正しく分類されているか。
  - regularity 6 件が precondition として genuine 消費されているか (load-bearing 再 bundle がないか)。
- [ ] verdict 全 OK ⇒ reclassify 確定 + handoff 明記。DEFECT ⇒ 当該 field を sorry-based に戻す。

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **本 plan の起点 (2026-05-29)**: 在庫 `parallel-gaussian-converse-multivariate-mi-inventory.md` が
   converse 2 件 (`bddAbove`/`max_ent`) を **self-buildable (真の Mathlib 壁でない)** と判定。
   `wall:multivariate-mi` は誤分類気味で "hard" でなく "big (~285-430 行)"。1-D 完成形
   `awgn_per_input_mi_le_log` (`@audit:ok`) の `Fin n` lift で genuine 着地可能。撤退ライン発動 NO を基本線とする。
2. **M0 instance 確認を独立工程化**: 在庫が「`CountableOrCountablyGenerated (Fin n → ℝ)` instance 有無 =
   1-turn リスク」と名指し。本 plan 策定時 loogle で named instance 0 件だが Pi/CountablyGenerated 継承で
   resolve 見込み。M0 で `infer_instance` 確認を先行させ、立たない場合のみ Phase 2 を `wall:multivariate-mi`
   staged 維持 (縮退案 (a))。
