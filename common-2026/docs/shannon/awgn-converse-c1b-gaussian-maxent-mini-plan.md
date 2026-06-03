# AWGN converse C-1b — per-letter Gaussian max-entropy 4 hyp 充足 mini 計画

> **Parent**: [`awgn-converse-aux-plan.md`](awgn-converse-aux-plan.md) §「Phase C — sum-form 構造での Phase C 統合」 C-1b 項 (~830-840 行)
>
> **Parent moonshot**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) §「撤退ライン F-3」
>
> **Sibling minis (現セッション並列候補)**: #M2 = C-1c Jensen / #M3 = C-5 transitive MI 有限性 (本 mini と独立、別 mini-plan で起草)

## ステータス

- **Slug**: `awgn-converse-c1b-gaussian-maxent`
- **対象 sorry 1 件**: `InformationTheory/Shannon/AWGNConverseDischarge.lean:616`
  `awgn_per_letter_mi_le_log_var` (現在 `@residual(plan:awgn-converse-aux-plan)`)
- **規模見込**: ~80-150 行 analytic work (親 §C-1b 内訳通り)
- **Mathlib 壁深度**: medium (`h_var_int` / `h_ent_int` の per-letter 充足が深度の上限要因)
- **session 見込**: 1-2 session
- **Phase A bundle predicate `PerLetterIntegrabilityForConverse` は本 mini 範囲外**
  (= staged hyp T-FFC-2、destructure するだけで `h_ent_int` 供給は受け取り側)

## 進捗

- [ ] M0 在庫確認 — Mathlib `differentialEntropy_le_gaussian_of_variance_le` 4 hyp +
      `gaussianReal_*` convolution / mean / variance + InformationTheory `perLetterYLaw` 形 verbatim 📋
- [ ] M1-Skeleton — `awgn_per_letter_mi_le_log_var` body の have-chain skeleton +
      per-letter helper signature 起草 (`sorry` 残置で型整合) 📋
- [ ] M2-Hyp供給 — 4 hyp (`hμ`/`h_mean`/`h_var`/`h_var_int`) を per-letter 形で genuine
      化 (`h_ent_int` は bundle destructure) 📋
- [ ] M3-Discharge — `differentialEntropy_le_gaussian_of_variance_le` 適用 + F-2
      bridge `h_mi_bridge_per_letter` + 結論型整形 `(1/2) log(1 + Var/N)` 📋
- [ ] M4-Verify — `lake env lean InformationTheory/Shannon/AWGNConverseDischarge.lean` silent
      + 当該 declaration 0 sorry / 0 @residual 📋

## ゴール / Approach

### Goal (target signature 再掲、変更不可)

```lean
-- InformationTheory/Shannon/AWGNConverseDischarge.lean:603-616 (現状)
theorem awgn_per_letter_mi_le_log_var
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P)
    (h_per_letter : PerLetterIntegrabilityForConverse P N h_meas c)
    (h_mi_bridge_per_letter :
        ∀ i : Fin n, (perLetterMI h_meas c i).toReal
          = InformationTheory.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
            - InformationTheory.Shannon.differentialEntropy
                (ProbabilityTheory.gaussianReal 0 N))
    (i : Fin n) :
    (perLetterMI h_meas c i).toReal
      ≤ (1 / 2) * Real.log (1 + perLetterInputSecondMoment c i / (N : ℝ)) := by
  sorry -- @residual(plan:awgn-converse-aux-plan)
```

### Approach (overall shape — 必須 §)

**戦略**: 「`h(Y_i) - h(Z_i)` 差分形」+「Gaussian max-entropy 4 hyp 形」の 2 段組合せ。

Mathlib-shape-driven (CLAUDE.md 規律): `differentialEntropy_le_gaussian_of_variance_le`
(`DifferentialEntropy.lean:518`) は結論型 `differentialEntropy μ ≤ (1/2) log (2πe v)` で、
**目的 `(1/2) log(1 + perLetterInputSecondMoment/N)` には直接成形できない**。差分形
`I(X_i; Y_i) = h(Y_i) - h(Y_i | X_i) = h(Y_i) - h(Z_i)` を **F-2 bridge hyp
`h_mi_bridge_per_letter` で外注供給** することで、Mathlib 結論形 `h(Y_i) ≤ (1/2) log(2πe(Var+N))`
を直接利用可能にする (差分形は本 mini 内で証明しない、bridge hyp として受け取る)。

数式 (1 行 in / 1 行 out 集約):

```
(perLetterMI).toReal  = h(Y_i) - h(gaussianReal 0 N)                              -- bridge hyp 供給
                     ≤ (1/2) log(2πe·v_Y) - (1/2) log(2πe·N)                      -- max-entropy 4 hyp 適用
                     = (1/2) log(v_Y / N)                                          -- log 差分集約
                     ≤ (1/2) log((perLetterInputSecondMoment + N) / N)             -- variance ≤ E[X²]+N
                     = (1/2) log(1 + perLetterInputSecondMoment / N)               -- 算術整形
```

**`v_Y := Var(Y_i)` の bound 経路** (variance vs second moment 区別 — verbatim 確認済):

- `perLetterInputSecondMoment c i := (1/M) ∑ₘ (c.encoder m i)²` (`AWGNConverseDischarge.lean:535`、
  **second moment** で variance ではない、mean は引かない)
- `Y_i = X_i + Z_i`, `Z_i ⊥⊥ X_i`, `Z_i ∼ gaussianReal 0 N` ⇒ `Var(Y_i) = Var(X_i) + N`
- `Var(X_i) = E[X_i²] - (E[X_i])² ≤ E[X_i²] = perLetterInputSecondMoment c i`
- ⇒ `Var(Y_i) ≤ perLetterInputSecondMoment c i + N`

Max-entropy lemma の `(v : ℝ≥0)` 引数には `(perLetterInputSecondMoment c i + (N : ℝ)).toNNReal`
を渡し、`hv : v ≠ 0` は `N > 0` から保証 (`hN : (N : ℝ) ≠ 0` + `N.coe_nonneg`)。

**bridge hyp の役割明示** (load-bearing vs regularity の判定軸 — CLAUDE.md 検証の誠実性):

- `h_mi_bridge_per_letter : ∀ i, (perLetterMI h_meas c i).toReal = h(Y_i) - h(gaussianReal 0 N)`
  は **F-2 plan (`awgn-mi-bridge-plan.md` / `awgn-mi-decomp-plan.md`) で genuine 化想定の
  外注 hyp**。結論型は `awgn_converse` 結論 `log M ≤ n·C + binEntropy + …` とは **無関係**
  (中間量 = per-letter MI の差分公式)、**regularity (Mathlib 壁 packaging)** に分類。
  本 mini 内で discharge しない (姉妹 plan 委譲)。

### Mathlib 結論形が直接使えない箇所 → 別補題化 (sorry 退路)

`Var(Y_i) ≤ E[X_i²] + N` の **claim 補題** (`perLetterYLaw_variance_le` 仮称) は
`perLetterYLaw h_meas c i` の closed-form が mixture-of-Gaussians `(1/M) ∑ₘ
gaussianReal (c.encoder m i) N` であることに依存。Mathlib 直接 lemma は無く、本 mini 内で
~30-60 行の self-derive が要る (mean-zero noise + independence)。失敗時は別 `sorry` +
`@residual(plan:awgn-converse-aux-plan)` で T-FFC-2 staged を 1 件追加 (規模超過 mitigation、§撤退ライン参照)。

## Mathlib + InformationTheory 在庫 (M0、verbatim、本 mini で利用するもの全列挙)

CLAUDE.md「具体的数値・型予測の verbatim 確認」遵守。signature は paraphrase 禁止、`[...]`
型クラス前提含む verbatim。

### 主用 — `differentialEntropy_le_gaussian_of_variance_le`

**InformationTheory/Shannon/DifferentialEntropy.lean:518**:

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

**hyp 6 個** (上記内訳、`[IsProbabilityMeasure μ]` 含む):

1. `[IsProbabilityMeasure μ]` (instance) — `μ := perLetterYLaw h_meas c i` で要求、
   `perLetterYLaw` が `(awgnConverseJoint).map (fun ω => ω.2 i)`、joint は
   `IsProbabilityMeasure` (`AWGNConverseDischarge.lean:78`)、`.map` で継承
   (`measurable_snd.aemeasurable` 経由)。
2. `hμ : μ ≪ volume` — `perLetterYLaw` の **mixture-of-Gaussians** 形 absolute continuity。
   各 mixture component `gaussianReal (c.encoder m i) N` ≪ `volume`
   (`gaussianReal_absolutelyContinuous` `Mathlib/Probability/Distributions/Gaussian/Real.lean:228`)、
   有限和 / convex combination で継承。
3. `m : ℝ` — `m := (1/M) ∑ₘ c.encoder m i` (uniform W 上 X_i mean、Z_i mean=0 から)。
4. `hv : v ≠ 0` — `v := (perLetterInputSecondMoment c i + (N : ℝ)).toNNReal`、
   `hN : (N : ℝ) ≠ 0` + `perLetterInputSecondMoment ≥ 0` から `v ≥ N > 0`。
5. `h_mean : ∫ x, x ∂μ = m` — per-letter Y_i mean 計算 (X_i mean + 0)。
6. `h_var : ∫ x, (x - m)² ∂μ ≤ (v : ℝ)` — `Var(Y_i) = Var(X_i) + N ≤ E[X_i²] + N`。
7. `h_var_int : Integrable (fun x => (x - m)²) μ` — `μ` が mixture-of-Gaussians、
   each component の 2 次モーメント有限 (`gaussianReal` ≪ `volume` + Gaussian の moment 性)。
8. `h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume`
   — **bundle `PerLetterIntegrabilityForConverse` の field、destructure で受領**
   (Mathlib 壁 T-FFC-2 staged、本 mini で discharge しない)。

### 補助 — Gaussian 系 (Mathlib)

- `gaussianReal_absolutelyContinuous` `Real.lean:228`:
  `(μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : gaussianReal μ v ≪ volume`
- `gaussianReal_conv_gaussianReal` `Real.lean:613`:
  `{m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} : (gaussianReal m₁ v₁) ∗ (gaussianReal m₂ v₂)
     = gaussianReal (m₁ + m₂) (v₁ + v₂)`
- `gaussianReal_add_gaussianReal_of_indepFun` `Real.lean:624`:
  `{Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0}
   {X Y : Ω → ℝ} (hXY : IndepFun X Y P) (hX : P.map X = gaussianReal m₁ v₁)
   (hY : P.map Y = gaussianReal m₂ v₂) :
   P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂)`
- `variance_fun_id_gaussianReal` (in `Mathlib/Probability/Distributions/Gaussian/Basic.lean`、
  M0 で正確 line 確認) — `Var[id; gaussianReal m v] = v`

### InformationTheory 内 在庫

- `perLetterYLaw` `AWGNConverseDischarge.lean:104`:
  `(awgnConverseJoint h_meas c).map (fun ω => ω.2 i) : Measure ℝ`
- `perLetterMI` `AWGNConverseDischarge.lean:111` (canonical joint 形)
- `perLetterInputSecondMoment` `AWGNConverseDischarge.lean:535`:
  `(1 / (M : ℝ)) * ∑ m : Fin M, (c.encoder m i) ^ 2` (**second moment**、verbatim 確認済)
- `awgnConverseJoint.instIsProbabilityMeasure` `AWGNConverseDischarge.lean:78`
  (= `IsProbabilityMeasure (awgnConverseJoint h_meas c)`)
- `PerLetterIntegrabilityForConverse` `AWGNConverseDischarge.lean:147`:
  `∀ i, Integrable (fun y => Real.negMulLog ((perLetterYLaw h_meas c i).rnDeriv volume y).toReal) volume`
  (destructure で `h_per_letter i : Integrable ...` を取り出す形)

### 補助 — `loogle` で M0 時に追加確認すべき項目

(本起草時には index で軽く確認、M0 phase で再度回す)

- `loogle "Measure.map _ (gaussianReal _ _)"` — `perLetterYLaw` の閉じた形を mixture 形で
  得る経路 (`Measure.map_smul` + `Measure.map_finset_sum` + `Measure.map_prod_snd`
  類似)
- `loogle "ProbabilityTheory.variance _ ≤ _"` — `Var(X) ≤ E[X²]` 直接 lemma
  (なければ `variance_eq_integral` 経由で展開)
- `loogle "Integrable (fun x => (x - _)^2)"` — 2 次モーメント integrability の標準 lemma
  (Gaussian の memLp / moment 系)

## Sub-bound 引数表 (CLAUDE.md brief checklist 必須項目)

本 mini は **bundle `PerLetterIntegrabilityForConverse` を destructure するのみ**
(Phase C C-1b 本体)。bundle field は 1 つだけなので分離型 `P_cb` / `P_target` 対立は
発生しない。一応 destructure 経路を表で明示:

| Sub-bound | bundle source | destructure 形 | 要求 capacity 側 | 必要 bridge 補題 |
|---|---|---|---|---|
| `h_ent_int` (4 hyp #4) | `h_per_letter : PerLetterIntegrabilityForConverse P N h_meas c` (全称定義) | `h_per_letter i : Integrable (negMulLog (rnDeriv (perLetterYLaw h_meas c i) volume)).toReal volume` | (capacity 非依存、Mathlib 壁) | — (Mathlib 壁、staged 残置) |
| `hμ` / `h_mean` / `h_var` / `h_var_int` | bundle 外 (本 mini で genuine 化) | — | (capacity 非依存) | `perLetterYLaw` 構造 (mixture-of-Gaussians) |
| F-2 bridge | `h_mi_bridge_per_letter i` (本 mini の引数) | `h_mi_bridge_per_letter i : (perLetterMI ...).toReal = h(Y_i) - h(gaussianReal 0 N)` | (本 mini で `(1/2) log(1 + S²/N)` 形に集約) | F-2 plan `awgn-mi-bridge-plan.md` / `awgn-mi-decomp-plan.md` |
| `perLetterInputSecondMoment` non-negativity | 既存 `awgn_sum_per_letter_mi_le_n_capacity` body 内 `h_nn` (`AWGNConverseDischarge.lean:668-675`) | unfold + `Finset.sum_nonneg` | — | — (本 mini 内自己完結) |

**`P_target` 側引数なし** (converse 側は固定 capacity `P` で動く、achievability 側のような
sphere packing `P_cb < P` separation は不要)。Bundle destructure 後に `i` を渡すだけの
mechanical assembly。

## Phase 詳細

### M0 — 在庫確認 (~30 分)

- [ ] `differentialEntropy_le_gaussian_of_variance_le` の verbatim signature 再 Read
      (本起草時に確認済、M0 時に再度 paste 確認のみ)
- [ ] `gaussianReal_add_gaussianReal_of_indepFun` (`Real.lean:624`) の indepFun 形が
      AWGN per-letter `X_i + Z_i` の form と一致するか verbatim 確認
      (X_i の law が `c.encoder · i` の uniform-W push-forward = discrete law なので
      Gaussian 形ではなく **mixture-of-Gaussians** で `gaussianReal_add_*` 直適用不可
      ⇒ `perLetterYLaw` の closed-form 確立は別経路 = X_i marginal の `Measure.map`
      で push-forward + Gaussian convolution per-codeword、judgement 必要)
- [ ] `variance_fun_id_gaussianReal` 正確 line + `[NormedSpace ℝ ℝ]` 等の前提
- [ ] `loogle "ProbabilityTheory.variance _ _ ≤ _"` で `Var ≤ E[X²]` 直接 lemma 在庫
- [ ] **境界 case 確認** (CLAUDE.md「具体的数値・型予測の verbatim 確認」):
      `perLetterInputSecondMoment c i = 0` のときに変換式が consistent か
      (`c.encoder m i = 0 ∀ m` ⇒ `Var(Y_i) = N`、`(1/2) log(1 + 0/N) = (1/2) log 1 = 0`、
       `(perLetterMI).toReal ≤ 0` を貫けるか確認)

### M1 — Skeleton (~30 分)

- [ ] body `by` 内 have-chain skeleton を 6-8 段で配置 (各段 `sorry` 仮置き、型整合確認)
- [ ] 補助 helper 必要なら同 file 内 `private` で立てる (signature + sorry):
  - `private lemma perLetterYLaw_absolutelyContinuous (h_meas) (c) (i) : perLetterYLaw h_meas c i ≪ volume`
  - `private lemma perLetterYLaw_mean (h_meas) (c) (i) : ∫ y, y ∂(perLetterYLaw h_meas c i) = (1/M) ∑ₘ c.encoder m i`
  - `private lemma perLetterYLaw_variance_le (h_meas) (c) (i) (hN) : ∫ y, (y - mean)² ∂... ≤ perLetterInputSecondMoment c i + N`
  - `private lemma perLetterYLaw_var_integrable (h_meas) (c) (i) : Integrable (fun y => (y - mean)²) (perLetterYLaw h_meas c i)`
- [ ] `lake env lean InformationTheory/Shannon/AWGNConverseDischarge.lean` 0 errors (sorry warning のみ)

### M2 — Hyp 供給 (~60-90 分)

- [ ] `perLetterYLaw_absolutelyContinuous` body (~20-30 行): mixture form 展開 +
      各 Gaussian component が `≪ volume` を `Measure.AbsolutelyContinuous` の有限和保存で
      集約 (Mathlib 在庫不在なら `Measure.AbsolutelyContinuous` の constructor で直接組む)
- [ ] `perLetterYLaw_mean` body (~10-20 行): `(awgnConverseJoint ...).map (fun ω => ω.2 i)`
      に対し `integral_map` + joint mixture 展開 + 各 mixture component の Gaussian mean
- [ ] `perLetterYLaw_var_integrable` body (~10-20 行): mixture form + 各 Gaussian の
      `memLp 2` (`memLp_id_gaussianReal`) → `Integrable (· - m)²`
- [ ] `perLetterYLaw_variance_le` body (~30-60 行 — 本 mini の analytic 山場):
      mixture form `Var(Y) = E[Y²] - (E[Y])²`、各 mixture component で
      `E[(X_i + Z_i)²] = (X_i)² + N` (X_i は per-codeword constant、Z_i ~ N(0,N)),
      mixture 平均: `E[Y²] = (1/M) ∑ₘ ((c.encoder m i)² + N) = perLetterInputSecondMoment + N`、
      `Var(Y) = E[Y²] - (E[Y])² ≤ E[Y²] = perLetterInputSecondMoment + N`

### M3 — Discharge (~30-60 分)

- [ ] `awgn_per_letter_mi_le_log_var` body の have-chain 埋め:
  - 4 hyp 全揃いで `differentialEntropy_le_gaussian_of_variance_le` 適用 →
    `h(perLetterYLaw) ≤ (1/2) log(2πe(perLetterInputSecondMoment + N))`
  - `differentialEntropy_gaussianReal` (`DifferentialEntropy.lean` 既存) で
    `h(gaussianReal 0 N) = (1/2) log(2πe N)` (要 `N ≠ 0`)
  - bridge hyp `h_mi_bridge_per_letter i` 適用で `I = h(Y) - h(Z)` 形に
  - log 差分集約: `(1/2) log(2πe·v_Y) - (1/2) log(2πe·N) = (1/2) log(v_Y / N)`
    (要 `2πeN > 0` / `v_Y ≥ N > 0`、`Real.log_div`)
  - 算術整形: `v_Y / N = (S² + N) / N = 1 + S² / N` (要 `N ≠ 0`、`add_div`)
  - 単調性 (`Real.log_le_log_iff`): `v_Y ≤ S² + N` から `log(v_Y/N) ≤ log(1 + S²/N)`

### M4 — Verify

- [ ] `lake env lean InformationTheory/Shannon/AWGNConverseDischarge.lean` silent
      (0 errors、当該 declaration 0 sorry / 0 @residual)
- [ ] 当該 declaration の docstring から `@residual(plan:awgn-converse-aux-plan)` を **除去**
- [ ] 親 plan `awgn-converse-aux-plan.md` 進捗ブロック M1 ✅ 反映 (orchestrator 側で実施)

## 撤退ライン

| ID | 兆候 | mitigation |
|---|---|---|
| **M1-a** | M0 で `perLetterYLaw` の mixture closed-form が想定より hard (Mathlib `Measure.map_smul` / `Measure.map_finset_sum` 経由展開で type-class 整合不能) | `perLetterYLaw_*` helper 群を 1 つの集約 helper `perLetterYLaw_form` (closed-form 等式) に統合、4 helper を 1 helper + 3 推論補題に圧縮 |
| **M1-b** | `perLetterYLaw_variance_le` の self-derive が ~30-60 行を **超過** (≥ 100 行) | 本 helper を **staged hyp** 化 (bundle `PerLetterIntegrabilityForConverse` に 5 番目 field `variance_le` 追加、Phase A 再 publish が必要 = scope creep)。回避策として `Var(Y) ≤ E[X²] + N` claim を本 mini 内補題で `sorry + @residual(plan:awgn-converse-c1b-gaussian-maxent-variance)` で抜く (T-FFC-2 staged を 1 件追加 = 2 件に増、親 plan §C-1b 失敗時 fallback の sorry retreat 採用) |
| **M1-c** | `h_mi_bridge_per_letter` の per-letter 形が F-2 姉妹 plan で genuine 化していない / shape 不一致 | bridge hyp は本 mini の **引数** (= regularity packaging)、本 mini 内では「外注供給」前提で OK。shape mismatch 検出時は親 plan §risk 表 row 5 通り judgement ログで記録 |
| **M1-d** | mixture-of-Gaussians ≪ volume の Mathlib 在庫不在 (M0 で確認) | `Measure.AbsolutelyContinuous` constructor 直接組み (各 Borel `s` で `volume s = 0 → perLetterYLaw s = 0` を mixture decompose で集約)、~20-40 行で組める見込み |
| **M1-e** (致命) | M3 の log 差分集約で `Real.log_div` の `≠ 0` precondition 不成立 (= `N = 0` 退化想定外) | `hN : (N : ℝ) ≠ 0` から `2πeN > 0` を field_simp + positivity で導く plumbing (~5-10 行)、致命にはならない見込み |
| **M1-fallback (mini 全体)** | M0-M3 のいずれかで規模が中央予測 ~80-150 行を **大幅超過** (≥ 250 行) または analytic body が本質的に Mathlib 壁を 1 件以上追加 hit | **本 mini 全体を撤退**: body を `sorry + @residual(plan:awgn-converse-c1b-gaussian-maxent)` 残置 (現状 `@residual(plan:awgn-converse-aux-plan)` から **本 mini 固有 slug に絞り込み**)、親 plan §C-1b 失敗時 fallback "本補題を staged hyp 化して bundle に 4 番目 sub-bound 追加" (`awgn-converse-aux-plan.md` line 909-912) に降格。本 mini は閉じて後続 mini に委ねる |

**load-bearing 禁止規律** (CLAUDE.md「検証の誠実性」遵守):

- **禁止**: `awgn_per_letter_mi_le_log_var` の **結論型と等しい仮説** を引数に追加して
  body を `:= h` で抜く (循環 tier 5 defect)。signature は本 mini 内で **改変しない**
  (= 親 plan §C-1b で確定済の per-letter capacity 形)。
- **禁止**: `*Hypothesis` predicate に **本 mini の analytic 核** (例: `Var(Y) ≤ E[X²]+N`)
  を bundling して仮説として受け取り、body を機械的展開だけにする。bundle
  `PerLetterIntegrabilityForConverse` は `h_ent_int` (Mathlib 壁) のみを抱える
  **regularity bundle** であり、`Var(Y) ≤ ...` の analytic は本 mini 内で genuine 化する。
- 上記 M1-b mitigation で bundle に field 追加するのは **load-bearing 追加ではなく
  Mathlib 壁 packaging の拡張** (= regularity bundle の field 拡張) なので OK
  だが、判断ログで record 必須。

## 検証手順

```bash
lake env lean InformationTheory/Shannon/AWGNConverseDischarge.lean
```

期待出力 (M4 完了時):

- `0 errors`、`0 sorry` warning (当該 declaration `awgn_per_letter_mi_le_log_var`)
- 残置 sorry は他 declaration の `@residual(plan:awgn-converse-aux-plan)` (= C-1c / C-5 / etc.)
- `rg -n '@residual|@audit:' InformationTheory/Shannon/AWGNConverseDischarge.lean` で当該行が
  消えていることを確認

## 完了判定 (本 mini)

- [ ] `awgn_per_letter_mi_le_log_var` body genuine (0 sorry / 0 @residual)
- [ ] 親 plan §C-1b 進捗 ✅ 反映 (orchestrator 側、本 mini の責務外)
- [ ] proof-log: **no** (本 mini は親 plan §C の 1 sub-item、proof-log 単独不要、
      規模超過時のみ判断ログ append)
- [ ] **独立 honesty audit subagent 必須** (新規 helper `perLetterYLaw_*` 群導入 +
      M1-b/M1-fallback 発動時の bundle field 追加 / sorry 残置の classification 正しさ
      verify。orchestrator 側責務)

## 親 plan / 兄弟 mini との scope 区別

| Plan / mini | スコープ | 出力 | 状態 |
|---|---|---|---|
| `awgn-converse-aux-plan.md` (親) | Cover-Thomas 9.1.2 全体 converse (Fano + DPI + chain + per-letter Gaussian + Phase C 統合) | `AWGNConverseDischarge.lean` (823 行、Phase A-V 完走、5 sorry 残置) | Phase V 完走、後続 mini 群で残置 sorry を回収 |
| **本 mini (#M1)** | **C-1b per-letter Gaussian max-entropy 4 hyp 充足のみ** | 上記 file 内 `awgn_per_letter_mi_le_log_var` body | 起草中 (本 file) |
| #M2 (別 mini-plan) | C-1c Jensen / log 凹性集約 | 上記 file 内 `sum_log_one_add_le_n_log_one_add_avg` body | TBD (本 mini と独立、別 mini-plan で起草) |
| #M3 (別 mini-plan) | C-5 transitive MI 有限性 (`awgnConverseJoint_mutualInfo_ne_top_via_chain` 共通 helper) | 上記 file 内 helper + Fano helper の sorry 解消 | TBD |
| `awgn-mi-bridge-plan.md` / `awgn-mi-decomp-plan.md` (姉妹、F-2) | bridge `(perLetterMI).toReal = h(Y) - h(Z)` の genuine 化 | TBD | 起草中 (本 mini の外注 hyp `h_mi_bridge_per_letter` 供給元) |

## オーケストレータ注記

- 実装 agent は **`InformationTheory/Shannon/AWGNConverseDischarge.lean` 1 file のみ** 編集
  (`InformationTheory.lean` 編集なし、本 file は既に編入済)
- 本 mini と #M2 / #M3 は **同一 file** 内の別 declaration を触るため、**並列実行時は
  worktree 隔離必須** (CLAUDE.md `Parallel orchestration` 規律)。逐次 dispatch なら隔離不要。
- M1-b / M1-fallback 発動時は **bundle predicate signature 変更を伴うため Phase A
  再 publish 相当** = orchestrator 判断必要、実装 agent 単独で改変させない
- 完了時 orchestrator: (a) 親 plan §C-1b ✅ 反映、(b) `@residual` 除去確認、(c)
  独立 honesty audit subagent 起動 (CLAUDE.md「Independent honesty audit」必須条件発火)

## 判断ログ

書く頻度: M0-M4 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 例 (本 mini 起草時点では未発生、テンプレ):
1. **M0: `gaussianReal_add_gaussianReal_of_indepFun` 直適用不可** — X_i marginal が
   discrete law (codebook 上の uniform) で Gaussian ではないため、`perLetterYLaw`
   closed-form は mixture-of-Gaussians 形で別 derive 経路 (Approach 通り)。
2. **M1-b 発動**: `perLetterYLaw_variance_le` self-derive が 110 行に膨張、本 helper
   を staged 化 (bundle に field 追加)、親 plan §C-1b 失敗時 fallback に降格。
-->
