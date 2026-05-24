# EPI Stam inequality — discharge plan

> **Status**: 未着手 (Phase 設計済、2026-05-24 Wave 2 planner 起草)。本 plan は実装未着手だが
> Phase A–V の設計レベル shape が確定済。
> **Created**: 2026-05-24 (Wave 1.5 item #8、`epi-moonshot-plan` 76 件 slug 分割)。
> **Parent (history)**: [`epi-moonshot-plan.md`](./epi-moonshot-plan.md) (PASS-THROUGH publish 済、
> 撤退ライン L-EPI1+L-EPI2+L-EPI3 全採用、本 sub-plan は L-EPI1 = Stam inequality の genuine
> discharge を担当)。

## Position

- 親 moonshot: [`epi-moonshot-plan.md`](./epi-moonshot-plan.md) (Phase A-E publish 済、L-EPI1
  hypothesis pass-through)
- 関連 sub-plan:
  - [`epi-debruijn-integration-plan.md`](./epi-debruijn-integration-plan.md) — L-EPI2
    (de Bruijn integration) sister
  - [`epi-stam-to-conclusion-plan.md`](./epi-stam-to-conclusion-plan.md) — Stam + de Bruijn →
    EPI conclusion 合流部
- 関連 wall plan: [`fisher-info-moonshot-plan.md`](./fisher-info-moonshot-plan.md) / V2 系
  (Stam inverse-Fisher は Fisher info V2 経路の上流)
- 主入力 inventory:
  - [`epi-stam-blachman-discharge-inventory.md`](./epi-stam-blachman-discharge-inventory.md)
    (Stam Cauchy-Schwarz + Blachman score 経路、`condVar_ae_le_condExp_sq` 等)
  - [`epi-stam-condexp-score-discharge-mathlib-inventory.md`](./epi-stam-condexp-score-discharge-mathlib-inventory.md)
    (score function Mathlib API)

## Motivation

EPI moonshot は L-EPI1 (Stam inequality) を `IsStamInequalityHypothesis` predicate
hypothesis pass-through 形で publish (placeholder `Prop := True`)。一方で
**`EPIStamDischarge.lean` 内に既に `IsStamInequalityHyp` (genuine signature, V2 fisher info
keyed) が存在**しており、Stam discharge の真の作業は **既存 V1 primitive 全部を V2 に張替 + Blachman
score-of-convolution の真の証明**。Stam の核心 (`1/J(X+Y) ≥ 1/J(X) + 1/J(Y)`) を Cauchy-Schwarz +
λ-optimization + score convolution で構成し、Fisher info の inverse 形 inequality を確立する。

**前提条件 (重要)**: V2 Fisher info 経路 (`FisherInfoV2.lean`, `FisherInfoV2DeBruijn.lean`,
`FisherInfoV2DeBruijnBody.lean`, `FisherInfoV2HeatFlowBody.lean`) が 4 件とも
`@audit:suspect(fisher-info-moonshot-plan)` 状態 — 4 sub-predicate (`IsHeatSpatialDerivHyp` /
`IsHeatTimeDerivHyp` / `IsHeatFlowConvolutionHyp` / `IsIBPHypothesis`) decomposition は publish
済だが上流 wall。本 sub-plan は **V2 経路の sub-predicate 形を所与として** Stam inequality の
Cauchy-Schwarz/λ-optimization/score 経路を埋める設計。V2 の sub-predicate 自身は
`fisher-info-moonshot-plan` 側 (別 wall plan) の責務。並行可。

## Scope

担当 file 群 (W1-B `wave1-plan-sync-epi-bm.md` ベース):

| file | 役割 | suspect 件数 | LoC |
|---|---|---|---|
| `Common2026/Shannon/EPIStamDischarge.lean` | Stam discharge 主 follow-up | 15 | 686 |
| `Common2026/Shannon/EPIStamToBridge.lean` | Stam scaling decomposition + bridge wrappers | 14 | 663 |
| `Common2026/Shannon/EPIStamInequalityBody.lean` | Stam inequality body (Cauchy-Schwarz + AM-GM) | 5 | 479 |
| `Common2026/Shannon/EPIStamStep12Body.lean` | Stam Step 1+2 body (score convolution + Cauchy-Schwarz) | 5 | 356 |

**合計**: 39 件 suspect / 2184 LoC 既存 (sub-plan 起動時の closure target)。Phase A-D で増分予想 ~400-700 行。

- **Mathlib 壁 4 分類**: (b) 解析 — Stam inverse-Fisher inequality は Mathlib 不在 + Blachman
  score-of-convolution identity は Mathlib 不在 (`lconvolution` の微分可能性が `Found 0`)。
  V2 Fisher info 経路に依存。
- **Tier**: 3 (long-term)。
- **副入力**: `EPIStamInequalityBody.lean` 内に既に `stam_lambda_min` /
  `stam_inverse_form_of_harmonic_mean` 等の補助補題が用意されており、これらは **本 plan で再利用**。

## Closure criteria

- 各 declaration から Stam-hypothesis 引数を削除 (genuine discharge)、`IsStamInequalityHypothesis`
  (`EntropyPowerInequality.lean:138` の `Prop := True` placeholder) を本 plan の `IsStamInequalityHyp`
  (genuine signature) で置換。
- `@audit:suspect(epi-stam-discharge-plan)` を `@audit:ok` に降格 (39 件)。
- 連鎖効果: `epi-stam-to-conclusion-plan` 経由で EPI conclusion 23 件と連鎖閉 (合計 62 件)。

## ゴール / Approach

### 全体戦略

**Stam inequality** (Cover-Thomas Lemma 17.7.2):
```
1/J(X+Y) ≥ 1/J(X) + 1/J(Y)
```
where `J(W) = ∫ (logDeriv (pdf W))² · pdf W dx` (V2 Fisher info `fisherInfoOfDensity`)。

証明は 4 段:
1. **Blachman score-of-convolution identity**: `s_{X+Y}(z) = E[s_X(X) | X+Y=z]` (conditional
   expectation argument)
2. **Cauchy-Schwarz 適用**: 任意 `λ ∈ [0,1]` で `J(X+Y) ≤ λ² J(X) + (1-λ)² J(Y)`
3. **λ-optimization**: `λ_min = J(Y)/(J(X)+J(Y))` で最適化 → `J(X+Y) ≤ J(X)·J(Y)/(J(X)+J(Y))`
4. **inverse 形に書き直し**: `1/J(X+Y) ≥ 1/J(X) + 1/J(Y)`

**鍵となる構造選択** (Mathlib-shape-driven):

- **V2 Fisher info 経路**: `fisherInfoOfDensity (f : ℝ → ℝ) := ∫ (logDeriv f)² · f dx`
  形 (`FisherInfoV2.lean:88`)、Gaussian で正しく `1/v` を返す。本 plan の全 primitive は V2 keyed。
- **Blachman identity の Mathlib base**: `condExp_ae_eq_integral_condDistrib_id`
  (`Kernel/CondDistrib.lean`) + `IndepFun.pdf_add_eq_lconvolution_pdf` (`Density.lean:356`)。
- **conditional Cauchy-Schwarz**: `condVar_ae_le_condExp_sq` (`CondVar.lean:127`、
  `Var[g; μ | m] ≤ᵐ E[g² | m]`)。Blachman の `(E[g|G])² ≤ E[g²|G]` の実体。
- **λ-optimization**: 既存 `stam_lambda_min` (`EPIStamInequalityBody.lean`) を再利用、IVT 不要
  (`λ_min = J(Y)/(J(X)+J(Y))` は閉形)。

### Approach 図

```
[V2 Fisher info 経路 (前提)]                    [Mathlib 既存 (利用)]
  ─────────────────────                            ──────────────────
  FisherInfoV2.lean                                IndepFun.pdf_add_eq_lconvolution_pdf
  fisherInfoOfDensity                              condExp_ae_eq_integral_condDistrib_id
  IsRegularDensityV2                               condVar_ae_le_condExp_sq
  IsHeatFlowConvolutionHyp                         hasDerivAt_integral_of_dominated_loc_of_deriv_le

       ▲                                                  ▲
       │ sub-predicate decomp                             │ Blachman / Cauchy-Schwarz core
       │                                                  │
       └──────────────────────┬───────────────────────────┘
                              ▼
              Phase A — inventory + V1→V2 張替 ~30-50 行
                              ▼
              Phase B — Blachman score convolution ~120-200 行
                              ▼
              Phase C — Cauchy-Schwarz + λ-optimization ~60-100 行
                              ▼
              Phase D — inverse-Fisher harmonic mean 合成 ~80-120 行
                              ▼
              Phase V — verify + Common2026.lean 編入
                              ▼
              Stam inequality (genuine) → epi-stam-to-conclusion 入口
```

### 段階的 ship 設計 (Tier 0 / 1 / 2)

- **Tier 0** (Phase A + B 一部): V1→V2 張替 + Blachman skeleton。partial publish 価値あり
  (`IsStamScoreConvolution` を `True` から実 Prop へ昇格)。
- **Tier 1** (Phase A + B + C): Cauchy-Schwarz + λ-optimization まで。`IsStamCauchySchwarz` /
  `IsStamCauchySchwarzOptimal` を flaw-vacuous discharge から genuine discharge へ昇格。
- **Tier 2** (Phase A + B + C + D): Stam inequality genuine signature 完成、
  `IsStamInequalityHyp` を 0-sorry genuine theorem に。

### 規模見積もり

| Phase | 自作要素 | 想定行数 |
|---|---|---|
| A | V1→V2 張替 + Cauchy-Schwarz / AM-GM inventory | ~30-50 |
| B | Blachman score-of-convolution identity (smooth density 経路) | ~120-200 |
| C | λ-optimization + Cauchy-Schwarz inequality 適用 | ~60-100 |
| D | inverse-Fisher 合成 (harmonic mean → 1/J(X+Y) ≥ 1/J(X) + 1/J(Y)) | ~80-120 |
| V | verify + Common2026.lean 編入 + roadmap | ~5-10 |
| **合計** | | **~295-480** |

中央予測 **~400 行**。Stam 単独で `EPIStamInequalityBody.lean` + `EPIStamStep12Body.lean` +
`EPIStamDischarge.lean` の 3 file に分散追記、`EPIStamToBridge.lean` は scaling helper 再利用。

---

## 進捗

- [ ] Phase A — V1→V2 張替 + Cauchy-Schwarz inventory 📋
- [ ] Phase B — Blachman score-of-convolution identity 📋
- [ ] Phase C — λ-optimization + Cauchy-Schwarz application 📋
- [ ] Phase D — inverse-Fisher harmonic mean 合成 📋
- [ ] Phase V — verify (`lake env lean ...`) + Common2026.lean 編入 📋

proof-log: yes (各 Phase 完了時に `docs/shannon/proof-log-epi-stam-discharge-phase-*.md` を残す)

---

## Phase A — V1→V2 張替 + Cauchy-Schwarz inventory 📋

### スコープ

`EPIStamDischarge.lean` / `EPIStamInequalityBody.lean` / `EPIStamStep12Body.lean` /
`EPIStamStep3Body.lean` 内の **V1 `Common2026.Shannon.fisherInfo` 参照を V2
`fisherInfoOfMeasureV2` に張替**。inventory §1A 表で「V1 参照」と記された 5 件 (`IsStamCauchySchwarz`
/ `IsStamCauchySchwarzOptimal` / `IsStamCondExpCSHyp` / `IsStamTotalExpectation` /
`IsStamInequalityHyp`) が対象。`IsStamInequalityHyp` (V2 keyed) は既に
`EPIStamDischarge.lean:50-103` に存在、V1 keyed 旧版は廃止。

加えて Mathlib `MeasureTheory.integral_mul_le_L2_norm_mul_L2_norm` 系 + `Real.inner_mul_le_norm_mul_norm`
の verbatim signature を inventory file に追記、ローカル namespace alias を整える。

### Approach

V1→V2 張替えはほぼ機械的だが **`HasPDF X P volume` typeclass 漏れ**に注意 (V2 は密度を明示
引数として取るので、`pdfReal X` を取り出す `HasPDF` 前提が新規に必要)。EPI top-level signature
を質的後退させないために、V2 primitive の signature を **`(fX fY fXY : ℝ → ℝ)` 明示引数**
形にし、`HasPDF` は呼び出し側で必要に応じて供給する。これは既に `EPIStamDischarge.lean:50`
の `IsStamInequalityHyp` で採用済の流儀。

### Done 条件

- V1 keyed primitive 5 件すべて V2 keyed signature に置換。
- 旧 `_of_gaussian_fisherInfo_zero` / `_of_fisherInfoReal_zero` /
  `entropy_power_inequality_gaussian_via_stamDeBruijn` 系 (flaw-vacuous discharge) は既に削除済
  (2026-05-20 RESOLVED) を確認。
- inventory file に Cauchy-Schwarz / AM-GM の verbatim signature 追記。
- 0 sorry / 0 warning (`lake env lean EPIStamDischarge.lean`)。

### ステップ

- [ ] **A-0**: 既存 V1 keyed primitive を grep で列挙 (`rg -n 'Common2026.Shannon.fisherInfo' Common2026/Shannon/EPIStam*.lean`)
- [ ] **A-1**: V1 keyed `IsStamCauchySchwarz` (`EPIStamInequalityBody.lean:134`) を V2 形に置換
- [ ] **A-2**: V1 keyed `IsStamCauchySchwarzOptimal` (`EPIStamInequalityBody.lean:237`) を V2 形に置換
- [ ] **A-3**: V1 keyed `IsStamCondExpCSHyp` (`EPIStamStep12Body.lean:214`) を V2 形に置換
- [ ] **A-4**: V1 keyed `IsStamTotalExpectation` (`EPIStamStep3Body.lean:152`) を V2 形に置換
- [ ] **A-5**: Mathlib `MeasureTheory.integral_mul_le_L2_norm_mul_L2_norm` /
      `Real.inner_mul_le_norm_mul_norm` / `integral_pow_le_norm_pow` の verbatim signature を
      inventory に追記
- [ ] **A-6**: `lake env lean Common2026/Shannon/EPIStamDischarge.lean` clean

### 撤退ライン

- **L-Stam-A-α** (許容): V1 keyed primitive の一部が下流で大量に参照されている場合、
  V1↔V2 bridge lemma (`fisherInfo_to_V2_via_pdfReal`) を 1 本書いて pass-through し、本格的
  置換は Phase D まで持ち越す。これは **honest** (前提として明示)、`:True` 化はしない。

---

## Phase B — Blachman score-of-convolution identity 📋

### スコープ

`EPIStamStep12Body.lean` 内の `IsStamScoreConvolution` (現状 `:= True` placeholder、
`EPIStamInequalityBody.lean:104`) を **真の Blachman identity** に置換:

```
s_{X+Y}(z) = E[s_X(X) | X+Y=z]   (a.e. z under pdf(X+Y))
```

ここで `s_W(w) := logDeriv (pdfReal W) w`。

### Approach

Mathlib base 3 本の合成:

1. **`IndepFun.pdf_add_eq_lconvolution_pdf'`** (`Density.lean:349`、σ-finite 明示版):
   `pdf (X+Y) ℙ μ =ᵐ[μ] pdf X ℙ μ ⋆ₗ[μ] pdf Y ℙ μ`
2. **`hasDerivAt_integral_of_dominated_loc_of_deriv_le`** (`ParametricIntegral.lean:289`):
   積分記号下微分 (`F z x := p_X(x) · p_Y(z-x)` を立てて dominated 仮定を整える)
3. **`condExp_ae_eq_integral_condDistrib_id`** (`Kernel/CondDistrib.lean`):
   `μ[s_X(X) | X+Y] =ᵐ ∫ s_X(x) · p_X(x) · p_Y((X+Y)-x) / p_{X+Y}(X+Y) dx`

**核心**: 畳み込み密度 `p_{X+Y}(z) = ∫ p_X(x) · p_Y(z-x) dx` の `logDeriv` は
`p'_{X+Y}(z) / p_{X+Y}(z) = ∫ p'_X(x) · p_Y(z-x) dx / p_{X+Y}(z)`
であり、これは `s_X(x) · p_X(x) · p_Y(z-x) / p_{X+Y}(z)` の `x` についての積分 = `E[s_X(X) | X+Y=z]`
に等しい (Blachman identity)。

**注意 (inventory §2C より)**: `lconvolution` の微分可能性は Mathlib `Found 0` — `F z x := p_X(x) · p_Y(z-x)`
を立てて `hasDerivAt_integral_of_dominated_loc_of_deriv_le` を直接適用する経路は **dominated
bound の構築** が自前。Gaussian-mollified 密度 (heat-kernel smoothed) でない一般密度では
微分可能性自体が成り立たない可能性 → 撤退ライン B-α (smooth density witness 仮定追加) を用意。

### Done 条件

- `IsStamScoreConvolution X Y P` を `Prop := True` から **真の Blachman identity 形** Prop に置換
- 単純なケース (smooth density 仮定下) で `blachman_identity_of_smooth` を完済
- 一般ケースは smooth density witness を hypothesis として残す (honest 撤退、`:True` 化は禁止)

### ステップ

- [ ] **B-1**: 畳み込み密度の存在 + 微分可能性 (smooth density witness 仮定下):
  ```
  theorem pdf_add_eq_smooth_convolution
      (X Y : Ω → ℝ) (h_smooth_X : ∀ x, 0 < pdfReal X x) (h_diff_X : Differentiable ℝ (pdfReal X))
      (h_smooth_Y : ...) (hXY : IndepFun X Y P) :
      ∀ z, pdfReal (X + Y) z = ∫ x, pdfReal X x * pdfReal Y (z - x) ∂volume
  ```
  ~30-50 行
- [ ] **B-2**: 畳み込み密度の `logDeriv` 表現 (積分記号下微分):
  ```
  theorem logDeriv_pdf_add_eq_integral
      ... : logDeriv (pdfReal (X+Y)) z = ∫ x, deriv (pdfReal X) x * pdfReal Y (z-x) ∂volume / pdfReal (X+Y) z
  ```
  ~30-50 行
- [ ] **B-3**: 条件付き期待値形に書き直し (`condExp_ae_eq_integral_condDistrib_id`):
  ```
  theorem score_of_sum_eq_condExp_score
      ... : (fun z => logDeriv (pdfReal (X+Y)) z) =ᵐ μ[s_X(X) | (X+Y)]
  ```
  ~30-50 行
- [ ] **B-4**: `IsStamScoreConvolution` を `:= True` から実 Prop に置換、上記 B-3 を完済の場合
      `_of_smooth` 形で hypothesis-free discharge (一般ケースは smooth witness 仮定で外出し)。
      ~30-50 行

### 撤退ライン

- **L-Stam-B-α** (許容): 畳み込み密度の微分可能性 (`lconvolution` Mathlib gap) を smooth density
  witness hypothesis `IsScoreConvolutionWitness X Y P f_X f_Y` で外出し。docstring で
  "NOT a discharge / load-bearing on smooth-density assumption" を明示。`:True` 化禁止、
  `:= IsBlachmanIdentity X Y P` 等の循環禁止。**honest 命名規律**: `IsBlachmanIdentityHyp_smooth`
  等、smooth-density 仮定であることを type 名で明示。

---

## Phase C — λ-optimization + Cauchy-Schwarz application 📋

### スコープ

`EPIStamInequalityBody.lean` 内 `IsStamCauchySchwarz` / `IsStamCauchySchwarzOptimal` を
**Blachman identity (Phase B) から Cauchy-Schwarz を適用** して **flaw-vacuous discharge から
genuine discharge へ昇格**。λ-optimization は既存 `stam_lambda_min` /
`stam_inverse_form_of_harmonic_mean` (補助補題) を再利用。

### Approach

Cauchy-Schwarz の core 不等式:

```
J(X+Y) = ∫ (s_{X+Y}(z))² · p_{X+Y}(z) dz
       = ∫ (E[λ·s_X(X) + (1-λ)·s_Y(Y) | X+Y=z])² · p_{X+Y}(z) dz    -- Blachman
       ≤ ∫ E[(λ·s_X(X) + (1-λ)·s_Y(Y))² | X+Y=z] · p_{X+Y}(z) dz    -- 条件付き Jensen
       = E[(λ·s_X(X) + (1-λ)·s_Y(Y))²]
       = λ²·E[s_X(X)²] + (1-λ)²·E[s_Y(Y)²]                           -- 独立性 + score expect=0
       = λ²·J(X) + (1-λ)²·J(Y)
```

**Mathlib base**: `condVar_ae_le_condExp_sq` (`CondVar.lean:127`、`(E[g|G])² ≤ E[g²|G]`) を
`g = λ·s_X(X) + (1-λ)·s_Y(Y)` に適用、両辺 `p_{X+Y}` で積分。クロス項 `λ·(1-λ)·E[s_X(X)·s_Y(Y)]`
は独立性 + `E[s_X(X)] = 0` (score expectation vanishes、`integral_logDeriv_density_eq_zero`
in `FisherInfoV2.lean:157`) で消える。

**λ-optimization**: `min_λ {λ²·J(X) + (1-λ)²·J(Y)} = J(X)·J(Y) / (J(X)+J(Y))` at
`λ_min = J(Y) / (J(X)+J(Y))`。既存 `stam_lambda_min` を import。

### Done 条件

- `IsStamCauchySchwarz X Y P` (`EPIStamInequalityBody.lean:134`) を **genuine discharge**
  (Phase B Blachman identity + `condVar_ae_le_condExp_sq` から導出)
- `IsStamCauchySchwarzOptimal X Y P` (`EPIStamInequalityBody.lean:237`) を λ_min 適用形で
  genuine discharge
- `IsStamCondExpCSHyp` (`EPIStamStep12Body.lean:214`、∀λ convex bound 形) も同様
- 0 sorry / 0 warning

### ステップ

- [ ] **C-1**: score expectation vanishes の bridge (`E[s_X(X)] = 0`):
  ```
  theorem integral_score_eq_zero_real
      ... : ∫ ω, logDeriv (pdfReal X) (X ω) ∂P = 0
  ```
  既存 `integral_logDeriv_density_eq_zero` の measure 版 wrapper。~20-30 行
- [ ] **C-2**: cross-term cancellation under independence (`E[s_X(X)·s_Y(Y)] = 0`):
  ~15-25 行
- [ ] **C-3**: 条件付き Cauchy-Schwarz の score 経路適用 (`condVar_ae_le_condExp_sq` →
      `(E[g|G])² ≤ E[g²|G]`):
  ~20-30 行
- [ ] **C-4**: `J(X+Y) ≤ λ²·J(X) + (1-λ)²·J(Y)` 不等式の genuine 証明 (`IsStamCauchySchwarz`
      discharge):
  ~20-30 行
- [ ] **C-5**: λ_min による最適化 (`stam_lambda_min` 再利用):
  ~10-15 行

### 撤退ライン

- **L-Stam-C-α** (許容): `condVar_ae_le_condExp_sq` の `MemLp X 2 μ` 前提充足が score
  関数の L² integrability に依存し、一般密度では非自明 (重テール密度で破れる)。Gaussian 等
  light-tail に限定する hypothesis `IsScoreLpHyp X P` を honest 命名で外出し。
- **L-Stam-C-β** (許容): λ-optimization の IVT が必要な経路 (`stam_lambda_min` で `λ_min`
  の閉形が取れない場合) → `stam_lambda_existence` honest hypothesis で外出し。**`:True` 禁止**、
  既存補助補題 (`stam_lambda_min` は閉形なので IVT 不要) のため通常は不要。

---

## Phase D — inverse-Fisher harmonic mean 合成 📋

### スコープ

`EPIStamDischarge.lean` 内 `IsStamInequalityHyp` (`:50-103`、V2 keyed genuine signature) を
**Phase B + Phase C の出力から完成**。具体的には:

```
J(X+Y) ≤ J(X)·J(Y) / (J(X)+J(Y))    -- Phase C output (harmonic mean upper bound)
     ↓
1 / J(X+Y) ≥ (J(X)+J(Y)) / (J(X)·J(Y)) = 1/J(X) + 1/J(Y)    -- inverse 形
```

### Approach

`stam_inverse_form_of_harmonic_mean` (既存補助補題、`EPIStamInequalityBody.lean` 内推定) を
import + Phase C 出力に適用。positivity 前提 (`0 < J(X)`, `0 < J(Y)`) は本 plan signature
で要求。

`IsStamInequalityHyp_of_primitives` (`EPIStamDeBruijnConclusion.lean:162`) は既に存在し
`(h_conv : IsStamScoreConvolution) (h_te : IsStamTotalExpectation) → IsStamInequalityHyp`
の形。Phase B で `h_conv` を genuine 化、Phase C で `h_te` を genuine 化したことで
**`isStamInequalityHyp_via_step3` (`EPIStamStep3Body.lean:258`) が genuine signature を直接出す**。

加えて `IsStamToEPIBridgeHyp` (`EPIStamDischarge.lean:304`、Csiszár scaling argument) を
`epi-stam-to-conclusion-plan` 側で discharge する **入口を整える** (本 plan は出口提供のみ、
bridge 自身は sister sub-plan)。

### Done 条件

- `IsStamInequalityHyp X Y P` を hypothesis-free `theorem` に格上げ
- Phase B + Phase C の output から `isStamInequalityHyp_via_step3` 等を経由して
  genuine discharge
- 39 件の `@audit:suspect(epi-stam-discharge-plan)` を `@audit:ok` に降格
- `isStamInequalityHypothesis_of_stamInequalityHyp` (`EPIStamDischarge.lean:109`、bridge to
  EntropyPowerInequality.lean placeholder) を確認 (本 plan の出口)

### ステップ

- [ ] **D-1**: harmonic mean inversion (`stam_inverse_form_of_harmonic_mean` を import):
  ~10-15 行
- [ ] **D-2**: `IsStamInequalityHyp` の genuine completion (Phase B + C → harmonic mean →
      inverse):
  ~30-50 行
- [ ] **D-3**: `EPIStamDischarge.lean` 15 件の `@audit:suspect` を `@audit:ok` に降格
      (各 declaration の hypothesis pass-through を Phase D-2 の出力で置換):
  ~30-50 行
- [ ] **D-4**: `EPIStamToBridge.lean` 14 件の `@audit:suspect` を `@audit:ok` に降格 (Stam
      scaling decomposition は Phase D-2 + 既存 scaling helper の組合せ):
  ~10-25 行 (主に rewrite)

### 撤退ライン

- **L-Stam-D-α** (許容、Phase B/C 撤退ライン依存): Phase B-α または C-α/β が発動した場合、
  `IsStamInequalityHyp` の discharge は smooth-density witness (B-α) または score-Lp
  witness (C-α) を hypothesis として残す **partial discharge**。docstring で
  "NOT a full discharge / depends on B-α, C-α" を明示、`:True` 禁止、hypothesis 名は
  `IsStamInequalityHyp_under_smooth_density` のように type 名で明示。

---

## Phase V — verify + Common2026.lean 編入 📋

### スコープ

- `lake env lean Common2026/Shannon/EPIStamDischarge.lean` clean (0 errors / 0 sorry /
  警告最小限)
- `lake env lean Common2026/Shannon/EPIStamToBridge.lean` clean
- `lake env lean Common2026/Shannon/EPIStamInequalityBody.lean` clean
- `lake env lean Common2026/Shannon/EPIStamStep12Body.lean` clean
- `lake env lean Common2026/Shannon/EPIStamStep3Body.lean` clean
- `Common2026.lean` import 確認 (既に import 済みのはず、追加なし)
- `docs/textbook-roadmap.md` T2-D Stam 行を `[x]` に
- `docs/shannon/epi-moonshot-plan.md` の split-into 注記を更新 (39 件 closure 完了)

### Done 条件

- 上記 5 file 全て `lake env lean` clean
- 39 件 `@audit:suspect(epi-stam-discharge-plan)` → `@audit:ok` 降格完了
- 連鎖クローズ用に `IsStamInequalityHyp` (genuine theorem) を **sister sub-plan**
  `epi-stam-to-conclusion-plan` の Phase A 入口にエクスポート

---

## 撤退ライン総覧 (honest 限定)

| slug | Phase | 内容 | hypothesis 名 (例) | 解除条件 |
|---|---|---|---|---|
| L-Stam-A-α | A | V1↔V2 bridge 経由で V1 keyed primitive を保持 | `fisherInfo_to_V2_via_pdfReal` | Phase D で完全置換 |
| L-Stam-B-α | B | 畳み込み密度の smooth witness 仮定 | `IsBlachmanIdentityHyp_smooth` | Mathlib `lconvolution` 微分可能性 PR or heat-kernel mollification |
| L-Stam-C-α | C | score 関数の L² integrability 仮定 | `IsScoreLpHyp X P` | tail 解析 (Gaussian 限定なら自動) |
| L-Stam-C-β | C | λ-optimization の IVT 仮定 (通常不要) | `stam_lambda_existence` | 既存閉形 `stam_lambda_min` で常に充足 |
| L-Stam-D-α | D | 上記 B-α/C-α が発動した場合の partial discharge | `IsStamInequalityHyp_under_smooth_density` | 上流撤退ラインの解除 |

**全撤退ライン共通規律**:
- **`Prop := True` placeholder 禁止** (inventory Part 1A で V1 primitive 1 本が既に `:= True`
  状態、Phase B で **必ず** 実 Prop 化)
- **結論型 ≡ 仮説型 + `body := h` (循環) 禁止** (`IsStamInequalityHypothesis_via_self` 等は
  禁止)
- **load-bearing hypothesis を完成と称する name laundering 禁止** (`*_discharged` /
  `*_full` 命名を使わない)
- 撤退ライン発動時は docstring で「NOT a discharge / load-bearing on <仮説名>」を必ず明示

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-24 Wave 2 planner Phase 起草**: stub plan (66 行、Phase 設計未起草) に Phase
   A-V を埋め込み。inventory `epi-stam-blachman-discharge-inventory.md` Part 1A の V1 keyed
   primitive 5 件を Phase A で V2 張替対象として確定、Part 1C 依存グラフから `IsStamTotalExpectation`
   と `IsStamScoreConvolution` を Phase B / C の主 deliverable として確定。V2 Fisher info
   経路 (4 sub-predicate `@audit:suspect(fisher-info-moonshot-plan)` 状態) は本 plan の
   **前提として明記**、並行可。3 sub-plan 依存関係は §Position に既存記述で十分整合。
