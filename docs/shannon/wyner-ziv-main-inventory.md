# Wyner–Ziv operational main theorem — API 在庫調査

> 対象: Wyner–Ziv lossy source coding with decoder side information の **operational main theorem** (Cover–Thomas Thm 15.9.1)。R_WZ(D) の **情報側**は `InformationTheory/Shannon/WynerZiv/` に完成済 (0 sorry)。本ファイルは operational code ↔ R_WZ(D) を繋ぐ **achievability + converse** に必要な API の在庫。
>
> **Parent plan**: [`wyner-ziv-moonshot-plan.md`](wyner-ziv-moonshot-plan.md) — **Status: CLOSED (scope-out)**。本調査は scope-out されている operational main を「復活させるなら何が要るか」を測る棚卸し。撤退ラインの扱いは §7 参照。
>
> 検証日: 2026-07-05 / commit `f7e628f3`。

---

## 1. 一行サマリ

**operational main で使う API のうち、下部 primitive (measure-theoretic MI / condMI / condEntropy / klDiv / condDistrib / typicality / binning / covering / Csiszár sum identity) は 100% が in-project (`InformationTheory/Shannon/**`) に既存。Mathlib には operational coding-theory は皆無 (loogle `Found 0`: Csiszar / rateDistortion / WynerZiv / typicalSet)。不足しているのは (a) WZ operational-achievable 述語の宣言、(b) achievability の binning+covering ハイブリッド本体、(c) converse の auxiliary-variable single-letterization 本体、(d) pmf 形 `wynerZivRatePmf` ↔ measure 形 `condMutualInfo` 差の橋。self-build は 7 項目、いずれも in-project atom の再配線 (Mathlib 壁ではない)。**

最大の危険所見: 既存 `csiszar_sum_identity` は `As Bs : Fin n → Ω → γ` の **同一アルファベット γ 版**。WZ converse は X (α) と Y (β) が別型の **heterogeneous Csiszár** を要求するため、そのまま流用できない (§4, §6, §9 参照)。加えて `condMutualInfo` は `[StandardBorelSpace X/Y] [Nonempty X/Y]` を **両変数側**に要求し、`[Fintype+MSC]` から自動導出されない (§4)。

---

## 2. operational main の最終形 (提案 / 未実装)

現状 WZ operational headline は **存在しない** (`WynerZiv/Basic.lean` docstring が参照する `WynerZivAchievability.lean` / `WynerZivConverse.lean` は削除済)。SW achievability (`slepian_wolf_full_rate_region_achievability`) と RD achievability (`rate_distortion_achievability`) の existential 形をクローンした提案形:

```lean
-- 【提案・未実装】operational-achievable 述語 (現状 in-project に不在)
def WynerZivAchievable
    (P_XY : Measure (α × β)) (d : DistortionFn α γ) (R D : ℝ) : Prop :=
  ∃ (M : ℕ → ℕ) (_ : ∀ n, 0 < M n)
    (c : ∀ n, WynerZivCode (M n) n α β γ),
    Filter.Tendsto (fun n ↦ Real.log (M n : ℝ) / n) Filter.atTop (𝓝 R) ∧
    Filter.Tendsto (fun n ↦ (c n).expectedBlockDistortion P_XY d)
      Filter.atTop (𝓝 D)             -- または limsup ≤ D + 誤り確率 → 0

-- 【提案・未実装】achievability leg
theorem wyner_ziv_achievability
    (P_XY : Measure (α × β)) (d : DistortionFn α γ) (R D : ℝ)
    (h_rate : wynerZivRateFactorizable U P_XY.pmf d D < R) :
    WynerZivAchievable P_XY d R D := by sorry  -- @residual(wall:wz-binning-covering)

-- 【提案・未実装】converse leg
theorem wyner_ziv_converse
    (P_XY : Measure (α × β)) (d : DistortionFn α γ) (R D : ℝ)
    (h_ach : WynerZivAchievable P_XY d R D) :
    wynerZivRateFactorizable U P_XY.pmf d D ≤ R := by sorry  -- @residual(wall:wz-auxiliary-singleletter)
```

証明戦略 (pseudo-Lean):

```
-- achievability: binning (SW) + covering (RD) の 2 段ハイブリッド
1.  encoder: X^n を jointly-typical covering codebook U^n で被覆   (RD: jointTypicalLossyEncoder)
2.  被覆した codeword index を bin に落とす (rate 削減)             (SW: binningMeasure, binning_collision_prob)
3.  decoder: (bin index, Y^n) から conditional-typical slice で U^n を復元  (SW: conditionalTypicalSlice_card_le)
4.  U^n と Y^n から f(U,Y) を再構成、distortion ≤ D+ε             (RD: distortionTypicalSet, source_avg_distortion_le_simpler)
5.  誤り確率 → 0: covering 失敗 (RD 指数) + bin 衝突 (SW 指数) の和 → 0

-- converse: n-letter single-letterization + auxiliary Uᵢ + Csiszár sum identity
6.  nR ≥ H(J) ≥ I(J; X^n) - I(J; Y^n)                              (DPI, encoder は決定的)
7.  chain rule + auxiliary Uᵢ := (J, Y^{i-1}) を identify           (bc_input_singleletterize 型)
8.  cross term を Csiszár sum identity で相殺                       (csiszar_sum_identity, ただし heterogeneous 版が要)
9.  ∑ [I(Xᵢ; Uᵢ) - I(Yᵢ; Uᵢ)] ≥ ∑ R_WZ(Dᵢ) ≥ n·R_WZ((1/n)∑Dᵢ)     (wynerZivRateFactorizable + 凸性 wynerZivRateFactorizable_convex_in_D)
10. antitone + Jensen で n·R_WZ(D) 到達                             (wynerZivRateFactorizable_antitone)
```

---

## 3. FOCUS 1 — statement に要る定義 (在庫 + gap)

### 3A. 既存の WZ 定義 (`InformationTheory/Shannon/WynerZiv/Basic.lean`)

| 概念 | 定義 (verbatim signature) | file:line | 状態 | 判定 |
|---|---|---|---|---|
| WZ block code | `structure WynerZivCode (M n : ℕ) (α β γ : Type*) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] where encoder : (Fin n → α) → Fin M ; decoder : Fin M × (Fin n → β) → (Fin n → γ)` | `Basic.lean:59` | ✅ 既存 | **statement に十分**。encoder は X-side のみ、decoder は (codeword, side-info Y^n) を取る = WZ 正しい |
| 期待ブロック歪 | `noncomputable def expectedBlockDistortion (c : WynerZivCode M n α β γ) (P_XY : Measure (α × β)) (d : DistortionFn α γ) : ℝ` | `Basic.lean:73` | ✅ 既存 | i.i.d. source `Measure.pi (fun _ => P_XY)` 上で積分。operational 述語の歪項にそのまま使える |
| 歪 nonneg | `theorem expectedBlockDistortion_nonneg (c) (P_XY) (d) : 0 ≤ c.expectedBlockDistortion P_XY d` | `Basic.lean:84` | ✅ 既存 | 補助 |
| pmf 制約集合 | `def WynerZivConstraint (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) : Set ((α × β × U → ℝ) × (U × β → γ))` | `Basic.lean:200` | ✅ 既存 | 情報側の feasible set (Markov + 歪 ≤ D) |
| pmf 形レート | `noncomputable def wynerZivRatePmf (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) : ℝ` | `Basic.lean:233` | ✅ 既存 | R_WZ(D) の raw 形 (sInf) |
| factorizable レート | `noncomputable def wynerZivRateFactorizable (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) : ℝ` | `FactorizableRate.lean:382` | ✅ 既存 | Cover–Thomas §15.9 が直接扱う形。**converse の帰着先はこれ** |
| MI marginals | `wzMarginalXY / wzMarginalXU / wzMarginalYU`, `wzMutualInfoXU / wzMutualInfoYU (q : α × β × U → ℝ) : ℝ` | `Basic.lean:102–120` | ✅ 既存 | pmf 形 I(X;U), I(Y;U)。単一 letter 段で使う |

### 3B. statement に要るが不在 (self-build)

| 概念 | 何が要るか | 状態 | 転写元 (verbatim) |
|---|---|---|---|
| **WZ operational-achievable 述語** | `WynerZivAchievable P_XY d R D : Prop` (§2 提案形) | ❌ **不在** | SW: `slepian_wolf_full_rate_region_achievability` の `∃ M, ∃ encoders/decoders, Tendsto rate, Tendsto error 0` (下記 3C) を 1-rate に縮小してクローン |
| **誤り確率 `wzErrorProb`** | code の再構成誤り確率 (SW `swErrorProb` 相当) | ❌ **不在** | SW: `swErrorProb (μ) {n M_X M_Y} (Xs Ys) (f_X f_Y) (d) : ℝ` (`Achievability.lean:45`) |
| **pmf ↔ measure 橋** | `wynerZivRateFactorizable U (P_XY as pmf) d D` と `condMutualInfo μ X U - condMutualInfo μ Y U` の同一視 | ❌ **不在** | RD: `klDiv_joint_eq_mutualInfo` (`Converse.lean:108`)、`mutualInfoPmf` ↔ `mutualInfo` の既存橋を WZ 3変数へ拡張 |

### 3C. 転写元 operational headline (verbatim)

**SW achievability** — `SlepianWolf/FullRateRegion/PairBound.lean:1041`:
```lean
theorem slepian_wolf_full_rate_region_achievability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX_full : iIndepFun (fun i ↦ Xs i) μ)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY_full : iIndepFun (fun i ↦ Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ_full : iIndepFun (fun i ↦ jointSequence Xs Ys i) μ)
    (hidentZ : ∀ i, IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    (hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : α × β, 0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    {R_X R_Y : ℝ}
    (hRX : InformationTheory.MeasureFano.condEntropy μ (Xs 0) (Ys 0) < R_X)
    (hRY : InformationTheory.MeasureFano.condEntropy μ (Ys 0) (Xs 0) < R_Y)
    (hRXY : entropy μ (jointSequence Xs Ys 0) < R_X + R_Y) :
    ∃ (M_X M_Y : ℕ → ℕ), (∀ n, 0 < M_X n) ∧ (∀ n, 0 < M_Y n) ∧
    ∃ (f_X : ∀ n, (Fin n → α) → Fin (M_X n)) (f_Y : ∀ n, (Fin n → β) → Fin (M_Y n))
      (d : ∀ n, Fin (M_X n) × Fin (M_Y n) → (Fin n → α) × (Fin n → β)),
      Filter.Tendsto (fun n ↦ Real.log (M_X n : ℝ) / n) Filter.atTop (𝓝 R_X) ∧
      Filter.Tendsto (fun n ↦ Real.log (M_Y n : ℝ) / n) Filter.atTop (𝓝 R_Y) ∧
      Filter.Tendsto (fun n ↦ swErrorProb μ (jointRV Xs n) (jointRV Ys n)
                          (f_X n) (f_Y n) (d n)) Filter.atTop (𝓝 0)
```
→ **判定: この existential shape を WZ に 1-rate 化してクローン可能**。WZ では `∃ M, ∃ (c : ∀ n, WynerZivCode (M n) n α β γ), Tendsto rate R ∧ (Tendsto/limsup distortion ≤ D)`。「side-info decoder」は WZ code に既に内蔵。

**RD achievability** — `RateDistortion/AchievabilityStrongTypicality.lean:184`:
```lean
theorem rate_distortion_achievability
    (P_X_pmf : α → ℝ) (d : DistortionFn α β) {D : ℝ}
    (qStar : α × β → ℝ) (hqStar_mem : qStar ∈ RDConstraint P_X_pmf d D)
    (hqStar_pos : ∀ p : α × β, 0 < qStar p)
    {R : ℝ} (hI_lt_R : mutualInfoPmf qStar < R)
    {ε' : ℝ} (hε' : 0 < ε') (ε_X ε_join ε_dist δ_kl δ_typ : ℝ)
    -- (…多数の caller-supplied slack 前提。§4 参照…)
    :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : LossyCode M n α β),
        c.expectedBlockDistortion ((rdAmbient qStar).map (iidXs 0)) d ≤ D + ε'
```
→ **判定: `∃N, ∀n≥N, ∃ code, distortion ≤ D+ε'` の形。ただし slack 前提が多く「witness form」に近い** (無条件形は perturbation 引数が別途要る)。WZ もこの「slack を caller に出す witness form」で着地させるのが現実的。

---

## 4. Key-preconditions box (事故が起きやすい前提)

- **`condMutualInfo` の型クラス** (`CondMutualInfo.lean:59`):
  ```lean
  noncomputable def condMutualInfo (μ : Measure Ω) [IsFiniteMeasure μ]
      [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
      (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) : ℝ≥0∞
  ```
  - **両変数 X, Y に `[StandardBorelSpace]` + `[Nonempty]` を要求**。条件付け側 Z は measurable のみで OK。
  - `[Fintype + MeasurableSingletonClass]` から `StandardBorelSpace` は自動導出されない (Countable+MSC→DiscreteMeasurableSpace→StandardBorel の chain は発火するが、WZ の auxiliary `U` は `Fintype` として引数受けなので明示 instance が要る)。
  - **親 plan の対処**: `attribute [local instance]` で discrete-measurable-space instance を file 限定で有効化 (SW/RD への波及ゼロ)。→ この方式を踏襲する。
- **`mutualInfo` の型クラス** (`MutualInfo.lean:36`): `mutualInfo (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞` = `klDiv (μ.map (X,Y)) ((μ.map X).prod (μ.map Y))`。**型クラス制約なし** (klDiv が全域)。converse の block 段は `mutualInfo` (無制約) で通せるが、per-letter の auxiliary `condMutualInfo` 段で StandardBorel が要る。
- **`csiszar_sum_identity` は同一アルファベット版** (`BroadcastChannel/ConverseGateway.lean:117`): `(As Bs : Fin n → Ω → γ)` かつ `[Fintype γ] [Nonempty γ]`。**X (α) と Y (β) が別型の WZ には非対応** → heterogeneous 版 self-build が要る (§6 gap)。
- **RD achievability の slack 前提** (`AchievabilityStrongTypicality.lean:97–132`): `hqStar_pos : ∀ p, 0 < qStar p` (full-support、`conditionalStronglyTypicalSlice_mass_ge` が要求)、`hε_X_lt_ε_join`、`h_rate_gap`、`h_jts_subset_dts`、`hδ_kl_dominates : 8|α||β|ε_X² ≤ δ_kl·qZ_min` 等。無条件化は perturbation (`(1-τ)qStar + τ·uniform`) 引数。WZ も full-support 前提付き witness form が第一着地。
- **`condEntropy` (measure 形)** (`Fano/Measure.lean:83`): `def condEntropy (μ : Measure Ω) [IsFiniteMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) : ℝ := ∫ y, ∑ x, negMulLog ((condDistrib Xs Yo μ y).real {x}) ∂(μ.map Yo)`。出力側 `X` に `Fintype+MSC` (⇒ StandardBorel 自動) を要求。SW/RD converse が全面採用。

---

## 5. FOCUS 2 — achievability transfer 資産

### 5A. SW binning 資産 (`SlepianWolf/`)

| 概念 | signature (verbatim, 結論形込) | file:line | 判定 |
|---|---|---|---|
| binning 測度 | `noncomputable def binningMeasure (α) [Fintype α] [MeasurableSpace α] (n M : ℕ) [NeZero M] : Measure ((Fin n → α) → Fin M)` | `Binning.lean:62` | ✅ **WZ の bin 割当にそのまま流用可** |
| bin 衝突確率 | `theorem binning_collision_prob {n M : ℕ} [NeZero M] {x x' : Fin n → α} (h : x ≠ x') : (binningMeasure α n M).real {f \| f x = f x'} = (M : ℝ)⁻¹` | `Binning.lean:106` | ✅ 流用可。bin 衝突指数の芯 |
| conditional typical slice | `noncomputable def conditionalTypicalSlice (μ) (Xs Ys) (n : ℕ) (ε : ℝ) (y : Fin n → β) : Set (Fin n → α)` | `ConditionalTypicalSlice.lean:51` | ✅ **decoder が Y^n から候補集合を絞る芯**。WZ では U^n を絞る形に読み替え |
| slice card 上界 | `theorem conditionalTypicalSlice_card_le (μ) [IsProbabilityMeasure μ] (Xs Ys) (hXs hYs) (hindepY_full) (hidentY) (hindepZ_full) (hidentZ) (hposY) (hposZ) (n) {ε} (y) : ((conditionalTypicalSlice μ Xs Ys n ε y).toFinite.toFinset.card : ℝ) ≤ Real.exp ((n:ℝ) * …)` | `ConditionalTypicalSlice.lean:140` | ✅ **binning-decode 誤り確率の指数**。WZ side-info decode の芯 |
| SW error prob | `noncomputable def swErrorProb (μ) {n M_X M_Y} (Xs Ys) (f_X f_Y) (d) : ℝ` | `Achievability.lean:45` | ✅ WZ `wzErrorProb` の雛形 |

### 5B. RD covering 資産 (`RateDistortion/`, `ConditionalMethodOfTypes/`)

| 概念 | signature (verbatim, 結論形込) | file:line | 判定 |
|---|---|---|---|
| joint-typical covering encoder | `noncomputable def jointTypicalLossyEncoder (μ) (Xs Ys) {M n} (hM : 0 < M) (ε) (c : Codebook M n β) : (Fin n → α) → Fin M` | `AchievabilityJointTypicalEncoder.lean:63` | ✅ **WZ の U^n covering encoder の芯**。β↦U に読み替え |
| distortion-typical set | `noncomputable def distortionTypicalSet (μ) (Xs Ys) (d) (n : ℕ) (ε δ : ℝ) : Set ((Fin n → α) × (Fin n → β))` | `AchievabilityJointTypicalEncoder.lean:97` | ✅ 流用可 |
| covering 成功 ⇒ 歪 ≤ | `theorem blockDistortion_le_of_mem_distortionTypicalSet (μ) (Xs Ys) (d) (n) (ε δ) {p} (h : p ∈ distortionTypicalSet …) : blockDistortion d n p.1 p.2 ≤ expectedJointDistortion μ (Xs 0) (Ys 0) d + δ` | `AchievabilityJointTypicalEncoder.lean:109` | ✅ 歪保証の芯 |
| covering 失敗確率上界 | `theorem encoder_failure_prob_le_exp_neg_M_avg (μ) (Xs Ys) {M n} (ε) (P_X) [IsProbabilityMeasure P_X] (p) [IsProbabilityMeasure p] : ∫ x, (1 - p.real {y \| (x,y) ∈ jointlyTypicalSet …})^M ∂P_X ≤ ∫ x, Real.exp (-(M:ℝ) * p.real {…}) ∂P_X` | `AchievabilityCodebookMatchProbability.lean:63` | ✅ **covering 失敗指数の芯** |
| codebook 平均 → 存在 | `theorem exists_codebook_low_avg {M n} (p) [IsProbabilityMeasure p] (f) {B} (h_avg : ∑ c, (codebookMeasure p M n).real {c} * f c ≤ B) : ∃ c, f c ≤ B` | `AchievabilityCodebookMatchProbability.lean:138` | ✅ pigeonhole 抽出 |
| source 平均歪上界 | `theorem source_avg_distortion_le_simpler (μ) (Xs Ys) (d) {M n} (hM : 0 < M) (ε) {δ} (hδ) (c) (P_X) [IsProbabilityMeasure P_X] : ∫ x, blockDistortion … ≤ (expectedJointDistortion … + δ) + distortionMax d * P_X.real {…}` | `AchievabilityAsymptoticFailureDecay.lean:203` | ✅ 歪の平均分解 |
| 指数減衰 | `lemma ceil_exp_mul_exp_neg_tendsto_atTop {R θ} (hRθ : θ < R) : Tendsto (fun n ↦ ⌈exp(nR)⌉ * exp(-nθ)) atTop atTop` / `exp_neg_tendsto_zero_of_tendsto_atTop` | `AchievabilityAsymptoticFailureDecay.lean:40,78` | ✅ rate-gap → 0 の芯 |
| **conditional 強典型 slice 質量下界** | `theorem conditionalStronglyTypicalSlice_mass_ge (μ) [IsProbabilityMeasure μ] (Xs Ys) (hXs hYs) (hindep_Z_pair : Pairwise fun i j ↦ jointSequence Xs Ys i ⟂ᵢ[μ] jointSequence Xs Ys j) (hident_Z) (hposZ) (hposX) (hposY) (hmarg_X) (hmarg_Y) {ε ε_X δ} (hε) (hε_X) (hε_X_lt_ε) (hδ) (qZ_min) (hqZ_min_pos) (hqZ_min_le) (hδ_dominates_kl : 8·\|α\|·\|β\|·ε_X² ≤ δ·qZ_min) : ∃ N, ∀ n, N ≤ n → ∀ x, x ∈ stronglyTypicalSet μ Xs n ε_X → Real.exp (-(n:ℝ)·(…)) ≤ (Measure.pi (fun _ ↦ μ.map (Ys 0))).real (conditionalStronglyTypicalSlice μ Xs Ys n ε x)` | `ConditionalMethodOfTypes/Mass.lean:1274` | ✅ **covering + 条件付き被覆の芯。side-info 被覆の質量下界**。WZ achievability の最深部 |

**判定サマリ (achievability)**: SW binning と RD covering の atom は「reusable as-is」がほぼ全部。**gap は「binning と covering を同一 code に合成する接着層」** — 単一 lemma は存在しない (§6 gateway atom)。

---

## 6. FOCUS 3 — converse transfer 資産

| 概念 | signature (verbatim, 結論形込) | file:line | 判定 |
|---|---|---|---|
| **Csiszár sum identity (同型 γ)** | `theorem csiszar_sum_identity (μ) [IsProbabilityMeasure μ] (As Bs : Fin n → Ω → γ) (hAs) (hBs) : ∑ i, condMutualInfo μ (fun ω (j:Fin i.val) ↦ As ⟨j,…⟩ ω) (Bs i) (fun ω (j:{j//i.val<j.val}) ↦ Bs j ω) = ∑ i, condMutualInfo μ (fun ω (j:{j//i.val<j.val}) ↦ Bs j ω) (As i) (fun ω (j:Fin i.val) ↦ As ⟨j,…⟩ ω)` | `BroadcastChannel/ConverseGateway.lean:117` | ⚠️ **同一アルファベット γ 版のみ**。WZ の X(α)/Y(β) 別型に非対応 → heterogeneous 版が gap |
| MI chain rule (fin) | `lemma mutualInfo_chain_rule_Y_fin (μ) [IsProbabilityMeasure μ] (W : Ω → γ) (Bs : Fin n → Ω → γ) (hW) (hBs) : mutualInfo μ W (fun ω j ↦ Bs j ω) = ∑ i, condMutualInfo μ W (Bs i) (fun ω (j:Fin i.val) ↦ Bs ⟨j,…⟩ ω)` | `ConverseGateway.lean:46` | ✅ 同型だが chain の雛形 |
| **auxiliary single-letterize (BC 入力)** | `theorem bc_input_singleletterize [NeZero M₂] (μ) [IsProbabilityMeasure μ] (W₂ : Ω → Fin M₂) (Xs : Fin n → Ω → α) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂) (hW₂ hXs hY₁s hY₂s) (h_memo) (h_deg_block) : condMutualInfo μ (fun ω j ↦ Xs j ω) (fun ω j ↦ Y₁s j ω) W₂ ≤ ∑ i, condMutualInfo μ (Xs i) (Y₁s i) (fun ω ↦ (W₂ ω, fun (j:Fin i.val) ↦ Y₂s ⟨j,…⟩ ω))` | `BroadcastChannel/Converse.lean:244` | ✅ **WZ auxiliary single-letterization の第一クローン元**。`Uᵢ := (W₂, Y-prefix)` の構造がそのまま WZ の `Uᵢ := (J, Y^{i-1})` に対応 (X/Y 別型対応済) |
| condMI 2変数 chain rule (X軸) | `theorem condMutualInfo_chain_rule_X_2var (μ) [IsProbabilityMeasure μ] (X_RV X'_RV Yo Wc) (hX hX' hYo hWc) (hWcY_fin : mutualInfo μ Wc Yo ≠ ∞) : condMutualInfo μ (fun ω ↦ (X_RV ω, X'_RV ω)) Yo Wc = condMutualInfo μ X_RV Yo Wc + condMutualInfo μ X'_RV Yo (fun ω ↦ (Wc ω, X_RV ω))` | `ChannelCoding/ConverseMemorylessChainRule.lean:164` | ✅ auxiliary 展開の atom (`[StandardBorelSpace X X' Y W]` 要) |
| condMI 2変数 chain rule (Y軸) | `theorem condMutualInfo_chain_rule_Y_2var {α' β'} [StandardBorel …] (μ) [IsProbabilityMeasure μ] (X_RV A B Wc) (hX hA hB hWc) (hWcX_fin : mutualInfo μ Wc X_RV ≠ ∞) : condMutualInfo μ X_RV (fun ω ↦ (A ω, B ω)) Wc = condMutualInfo μ X_RV A Wc + condMutualInfo μ X_RV B (fun ω ↦ (Wc ω, A ω))` | `ConverseMemorylessChainRule.lean:243` | ✅ 同上 |
| MAC single-letterize (memoryless) | `lemma condMutualInfo_singleletter_le_of_memoryless (μ) [IsProbabilityMeasure μ] (X₁s X₂s Ys) (hX₁s hX₂s hYs) (h_per_letter) (h_outputs) : (condMutualInfo μ (fun ω j ↦ X₁s j ω) (fun ω j ↦ Ys j ω) (fun ω j ↦ X₂s j ω)).toReal ≤ ∑ i, (condMutualInfo μ (X₁s i) (Ys i) (X₂s i)).toReal` | `MultipleAccess/Converse.lean:268` | ✅ 別の single-letterize テンプレ (memoryless Markov 前提) |
| RD n-letter single-letterize | `theorem rate_distortion_converse_n_letter_singleLetter [Fintype α…] [Fintype β…] {M n} [NeZero M] (hn : 0 < n) (c : LossyCode M n α β) (hencoder hdecoder) (d) (μ) [IsProbabilityMeasure μ] (Xs) (hXs) (hindep : iIndepFun (fun i ↦ Xs i) μ) (P_X) [IsProbabilityMeasure P_X] (hXs_law) (h_MI_block_finite) (h_MI_perletter_finite) {D} (hD) : (rateDistortionFunction (fun a b ↦ d a b) P_X D).toReal ≤ (1/(n:ℝ)) * Real.log (Fintype.card (Fin M))` | `RateDistortion/ConverseNLetter.lean:659` | ✅ **converse の全体骨格 (antitone+Jensen+superadd+DPI) のクローン元**。WZ は右辺を `(1/n)∑[I(Xᵢ;Uᵢ)-I(Yᵢ;Uᵢ)]` に置換 |
| condEntropy pi ≤ ∑ | `lemma condEntropy_pi_le_sum_condEntropy_per_letter {n} {α} [Fintype α…] {β} [Fintype β…] (μ) [IsProbabilityMeasure μ] (Xs Xhs) (hXs hXhs) : condEntropy μ (fun ω j ↦ Xs j ω) (fun ω j ↦ Xhs j ω) ≤ ∑ i, condEntropy μ (Xs i) (Xhs i)` | `ConverseNLetter.lean:422` | ✅ 流用可 |
| MI superadditive | `lemma mutualInfo_superadditive_of_indep {n} {α} [Fintype α…] {β} [Fintype β…] (μ) [IsProbabilityMeasure μ] (Xs Xhs) (hXs hXhs) (hindep : iIndepFun (fun i ↦ Xs i) μ) : (∑ i, (mutualInfo μ (Xs i) (Xhs i)).toReal) ≤ (mutualInfo μ (fun ω j ↦ Xs j ω) (fun ω j ↦ Xhs j ω)).toReal` | `ConverseNLetter.lean:532` | ✅ 流用可 |
| RD 凸性 (converse Jensen) | `theorem wynerZivRateFactorizable_convex_in_D` / `_unconditional` (凸性で ∑R_WZ(Dᵢ) ≥ n·R_WZ((1/n)∑Dᵢ)) | `FactorizableRate.lean:548` / `ConditionalEntropyConvexity.lean:374` | ✅ **converse の Jensen 段は情報側完成品をそのまま呼べる** |
| RD 単調性 | `theorem wynerZivRateFactorizable_antitone (P_XY) (d) {D D'} (hD : D ≤ D') (h_ne) (h_bdd) : wynerZivRateFactorizable U P_XY d D' ≤ wynerZivRateFactorizable U P_XY d D` | `FactorizableRate.lean:391` | ✅ antitone 段 |

**判定サマリ (converse)**: 骨格 (`rate_distortion_converse_n_letter_singleLetter` の antitone+Jensen+superadd+DPI 連鎖) と auxiliary 展開 (`bc_input_singleletterize`) はクローン可。**gap は (i) heterogeneous Csiszár、(ii) auxiliary `Uᵢ:=(J,Y^{i-1})` の identify を `wzMutualInfoXU/YU` へ落とす橋**。凸性・単調性・pmf 形の情報側は完成品を呼ぶだけ。

---

## 7. self-build が必要な要素 (優先度順)

| # | 要素 | 推奨実装 | 工数感 | 落とし穴 |
|---|---|---|---|---|
| 1 | **WZ operational-achievable 述語 `WynerZivAchievable`** + `wzErrorProb` | SW `slepian_wolf_full_rate_region_achievability` の existential を 1-rate 化してクローン | ~40–80 行 | distortion を `Tendsto (𝓝 D)` にするか `limsup ≤ D+ε` にするかで converse 側の帰着が変わる。SW は error→0、RD は distortion≤D+ε' — WZ は**両方** (誤り確率→0 かつ 歪≤D+ε) |
| 2 | **achievability binning+covering ハイブリッド本体** | encoder = RD `jointTypicalLossyEncoder` (U^n 被覆) → SW `binningMeasure` で bin 化。decoder = `conditionalTypicalSlice` (Y^n で U^n 復元) → `f(U,Y)` 再構成。誤り確率 = covering 失敗 (`encoder_failure_prob_le_exp_neg_M_avg`) + bin 衝突 (`conditionalTypicalSlice_card_le`) の和 | ~800–1500 行 | 2 段構成の誤り事象分解が単一 lemma 化されていない。SW の 4-way 分解と RD の covering 分解の**合成**が新規 |
| 3 | **converse auxiliary single-letterization 本体** | `rate_distortion_converse_n_letter_singleLetter` 骨格を流用、右辺を `bc_input_singleletterize` 型で `∑[I(Xᵢ;Uᵢ)-I(Yᵢ;Uᵢ)]` に置換、cross 項を Csiszár で相殺 | ~400–700 行 | auxiliary `Uᵢ:=(J,Y^{i-1})` の identify と `wzMutualInfoXU/YU` (pmf 形) への落とし込みが新規 |
| 4 | **heterogeneous Csiszár sum identity** | 既存 `csiszar_sum_identity` (同型 γ) を `As : Fin n → Ω → α`, `Bs : Fin n → Ω → β` の別型に一般化 | ~150–300 行 | 既存証明は `condMutualInfo_comm` + chain rule に依存。別型化で `condMutualInfo` の `[StandardBorelSpace]` を α, β 両方に要求 → local instance 追加 |
| 5 | **pmf 形 ↔ measure 形 R_WZ の橋** | `klDiv_joint_eq_mutualInfo` (RD `Converse.lean:108`) を WZ 3変数 (X,Y,U) へ。`wzMutualInfoXU U q` = `mutualInfo μ X U`、`wzMutualInfoYU U q` = `mutualInfo μ Y U` の同一視 | ~100–200 行 | pmf `q : α×β×U→ℝ` と empirical measure の対応。RD の `mutualInfoPmf`↔`mutualInfo` 橋を 3変数拡張 |
| 6 | **`condMutualInfo` の discrete StandardBorel local instance** | 親 plan 記載通り `attribute [local instance]` で `Fintype+MSC → DiscreteMeasurableSpace → StandardBorelSpace` を file 限定発火 | ~10–20 行 | SW/RD への波及ゼロを保つため file scope 厳守。`U` (auxiliary) の instance 忘れが最頻事故 |
| 7 | **auxiliary alphabet `U` の cardinality bound (Carathéodory)** `\|U\| ≤ \|α\|+1` | **別 plan へ分離** (親 plan の判断踏襲)。operational main は `U` を Fintype 引数で受けて済ませる | scope-out | main には不要。converse を `∀ U` にすれば bound は後付け |

---

## 8. Mathlib 壁の列挙 (`@residual(wall:…)` 候補)

Mathlib には operational coding-theory / method-of-types / Csiszár が **一切ない** (すべて in-project)。loogle name-substring 検索の 0-hit 実測:

| Mathlib 壁 | loogle 確認 (2026-07-05) | 帰結 |
|---|---|---|
| Csiszár sum identity | `Found 0 declarations whose name contains "Csiszar"` | in-project `csiszar_sum_identity` に依存 (同型版のみ、§6) |
| rate-distortion function | `Found 0 declarations whose name contains "rateDistortion"` | in-project `rateDistortionFunction` に依存 |
| Wyner–Ziv | `Found 0 declarations whose name contains "WynerZiv"` | 全面 self-build (in-project) |
| typical set / method of types | `Found 0 declarations whose name contains "typicalSet"` | in-project typicality stack に依存 |
| operational channel/source coding | (rg on `Mathlib/`: `SlepianWolf`/`jointlyTypical` → 0 files) | in-project |

**Mathlib primitive (既存、下部で使う)**:
- `klDiv (μ ν : Measure α) : ℝ≥0∞` — `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57` (`noncomputable irreducible_def`)。`mutualInfo`/`condMutualInfo` の芯。
- `condDistrib {_ : MeasurableSpace α} [MeasurableSpace β] (Y : α → Ω) …` — `Mathlib/Probability/Kernel/CondDistrib.lean:64` (`noncomputable irreducible_def`)。`condMutualInfo`/`condEntropy` の芯。
- KL chain rule (`ln_compProd_eq_add` 等) — `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean`。

→ **真の「壁」は Mathlib 側ではなく in-project atom の未実装** (§7 の #2/#3/#4)。**shared sorry-lemma 推奨**: achievability leg (#2) と converse leg (#3) をそれぞれ headline に `sorry + @residual(wall:wz-binning-covering)` / `@residual(wall:wz-auxiliary-singleletter)` で立て、内部 atom を段階的に discharge する (SW/RD が採った witness-form 段階着地パターン)。同一壁の分散を避けるため、heterogeneous Csiszár (#4) は `csiszar_sum_identity_hetero` として **1 本の shared sorry lemma に集約**推奨 (詳細 → `docs/audit/audit-tags.md`「Shared Mathlib walls」)。

---

## 9. 撤退ラインとの距離

親 plan [`wyner-ziv-moonshot-plan.md`](wyner-ziv-moonshot-plan.md) は **既に撤退済 (Status: CLOSED, scope-out)**:
> Wyner–Ziv main theorem (…achievability + converse) は scope-out。…「Distributed Source Coding mini-chapter (Slepian-Wolf + Wyner-Ziv convexity body)」として publish と確定済。

- **本調査は撤退済 scope の「復活」棚卸し**。親の撤退ラインは既に発動しており、operational main を復活させるには textbook-roadmap Ch.15 の scope 再開判断が前提 (docs-only agent の権限外)。
- **触れる撤退トリガー**: (a) heterogeneous Csiszár (#4) が想定外に重い、(b) binning+covering 合成 (#2) の誤り事象分解が SW/RD の単純合成で閉じない、のいずれか。
- **提案する新規 degenerate fallback 撤退ライン** (復活する場合):
  1. achievability / converse を各々 headline で立て、本体を `sorry + @residual(wall:wz-binning-covering)` / `@residual(wall:wz-auxiliary-singleletter)` で type-check done 着地 (hypothesis bundling 禁止、`:True` slot 禁止)。
  2. それでも stall する場合 → **full-support + factorizable + `U` Fintype 引数固定**の witness form まで縮退 (RD `rate_distortion_achievability` の slack-exposed 形と同格)。cardinality bound (#7) は最初から別 plan。
  3. さらに stall → operational main は再 scope-out のまま、information-side (完成済) の publish で確定 (親 plan の現状維持)。

---

## 10. gateway atom candidates (次段 dispatch 標的)

### achievability side

**最も不確実な atom**: **side-info conditional covering** — 「bin index + 側方情報 Y^n から被覆 codeword U^n を消失誤りで復元できる」の質量下界。
- 最近接転写元: `conditionalStronglyTypicalSlice_mass_ge` (`ConditionalMethodOfTypes/Mass.lean:1274`) + `conditionalTypicalSlice_card_le` (`SlepianWolf/ConditionalTypicalSlice.lean:140`)。
- 距離: 両者は「slice の質量下界」「slice card 上界」を別々に持つが、**covering 済 U^n が bin 内で Y-conditional に一意復元される**という結合 statement は不在。self-build 見積 ~**300–500 行** (両 lemma の合成 + 誤り事象の和集合上界)。
- 検証観点: RD covering (`encoder_failure_prob_le_exp_neg_M_avg`) の指数と SW bin 衝突 (`binning_collision_prob`) の指数が**同じ n スケールで両立**するか (rate split `R = I(X;U)-I(Y;U)` の 2 項分解が指数を分ける)。

### converse side

**最も不確実な atom**: **heterogeneous auxiliary Csiszár single-letterization** — `Uᵢ:=(J,Y^{i-1})` を identify し `∑[I(Xᵢ;Uᵢ)-I(Yᵢ;Uᵢ)]` の下界を得る段で、X(α)/Y(β) 別型の cross 項相殺。
- 最近接転写元: `bc_input_singleletterize` (`BroadcastChannel/Converse.lean:244`、auxiliary=`(W₂,Y-prefix)` 構造が WZ に酷似) + `csiszar_sum_identity` (`ConverseGateway.lean:117`、ただし同型 γ)。
- 距離: `bc_input_singleletterize` は X/Y 別型・auxiliary prefix 構造を既に持つので**骨格クローンは軽い (~150 行)**。ただし cross 項相殺に要る Csiszár が同型版のみ → **heterogeneous 版 self-build ~150–300 行**が gateway。
- 検証観点 (gateway-atom-first): 復活 dispatch の第一手は **heterogeneous `csiszar_sum_identity_hetero` を 1 本 `lean-implementer` に投げ**、既存同型版証明 (`condMutualInfo_comm` + chain rule 依存) が別型で通るか (= `[StandardBorelSpace α] [StandardBorelSpace β]` local instance で `condMutualInfo` が両側に効くか) を先に判定する。ここが通れば converse 全体は骨格クローンで閉じる公算大。
