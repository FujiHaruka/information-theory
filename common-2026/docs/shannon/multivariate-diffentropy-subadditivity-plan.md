# 多変量 differential entropy subadditivity discharge 計画 🌙

> **Parent**: (新規 family、近接 plan: [`differential-entropy-plan.md`](differential-entropy-plan.md) §E (1-D 完成済) / [`brunn-minkowski-closure-plan.md`](brunn-minkowski-closure-plan.md) §Phase 3 / [`parallel-gaussian-chain-rule-plan.md`](parallel-gaussian-chain-rule-plan.md) §撤退ライン D-1 / [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md) §Phase B-0)
>
> **位置づけ**: 2026-05-24 Wave 2 で起草。`Common2026/Shannon/MultivariateDiffEntropy.lean` (307 行、4 件 `@audit:suspect(differential-entropy-plan)`) + `AWGNAchievabilityDischarge.lean` (`@audit:staged(continuous-aep-gaussian)` 2 件) の load-bearing honest hyp を genuine discharge する新規 sub-plan。
>
> **slug 不整合の修正**: 4 件 suspect が指している `differential-entropy-plan` は 1-D 差分エントロピー plan (既に DONE-HONEST-HYPS で publish 済) で、n 変数 subadditivity の honest hyp bundle (`h_llr_split` Bayes density split + integrability 7 本) とは**無関係**。本 plan の slug `multivariate-diffentropy-subadditivity-plan` を新規 SoT として 4 件 suspect tag の付け替え対象とする (実装時に Edit 適用)。

## 進捗

- [x] Phase 0 — 在庫確認 + suspect tag slug 整合 ✅ (2026-05-25, commit `0fe2ad4`)
- [x] Phase 1 — 2 変数 subadditivity bridge の honest hyp 縮約 (`h_llr_split` Bayes density split を `prod_withDensity` + `volume_eq_prod` で discharge) ✅ (2026-05-25, commit `0fe2ad4`、`_v2` で genuine 化)
- [ ] Phase 2 — n 変数 subadditivity 完全 genuine 化 🔄 **re-opened 2026-05-29** (前回 Wave 3 withdrawal は gap を誤診、判断ログ #2026-05-29 参照)。2 段着地: **2a** structural bridge genuine + density split 1 点 sorry / **2b** density split discharge で完全 closure
  - [ ] Phase 2a — structural bridge genuine 化 (density split を独立 sorry 補題に切出し) 📋
  - [ ] Phase 2b — density split を genuine discharge (= 0 sorry 完全 closure) 📋
- [x] Phase 3 — AWGN `IsContinuousAEPGaussian` predicate の plan-side reflection (Mathlib 壁 = continuous SMB / n-dim differentialEntropy、staged 維持) ✅ (2026-05-25, commit `0fe2ad4`)
- [x] Phase V — clean + slug 付け替え ✅ (2026-05-25, commit `0fe2ad4`、2 件 `superseded-by(<v2>)` + 2 件 `suspect(multivariate-diffentropy-subadditivity-plan)` 残置)

## ゴール / Approach

**ゴール**: `MultivariateDiffEntropy.lean` の 4 件 honest load-bearing hyp を **削減 or genuine 化**し、`jointDifferentialEntropy_le_sum` (2 変数) / `jointDifferentialEntropyPi_le_sum` (n 変数) の `h_llr_split` (Bayes density split) を `prod_withDensity` (Mathlib 既存) + `rnDeriv_withDensity` (Mathlib 既存) で **discharge** する。AWGN 側 `IsContinuousAEPGaussian` (`AWGNAchievabilityDischarge.lean:140`、`@audit:staged(continuous-aep-gaussian)`) は Mathlib 壁 = continuous SMB / n-dim differentialEntropy 不在で **staged 維持** が現実的、その判定を本 plan で明示。

**Approach (戦略の shape)** — 既存 inventory (`multivariate-diffentropy-inventory.md`) の判定 (実現可能性 = CONDITIONAL with honest 仮定) を 2 段で詰める。

1. **2 変数 bridge を genuine 化 (Phase 1, 中規模)**。現状 `klDiv_prod_marginals_toReal_eq_sum_sub_joint` (`MultivariateDiffEntropy.lean:90`) は `h_llr_split` (`llr(joint ‖ μ_X ⊗ μ_Y) =ᵐ[μ] log(rnDeriv joint) - log(rnDeriv μ_X) - log(rnDeriv μ_Y)`) を honest hyp で受けている。これを Mathlib `prod_withDensity` (`Mathlib/MeasureTheory/Measure/WithDensity.lean:712`、verbatim 存在) + `rnDeriv_withDensity` (Mathlib 既存) + `Measure.volume_eq_prod` (`rfl`) で genuine に produce する。bridge の数学的核 = `KL ≥ 0` (`mutualInfo_nonneg`, `ENNReal.toReal_nonneg`) は既に genuine。残るは density split の **配線**だけで Mathlib 壁ではない (inventory §B 判定)。

2. **n 変数 bridge は 2 変数 induction か `pi_withDensity` 自作 (Phase 2, 最大リスク)**。`klDiv_pi_marginals_toReal_eq_sum_sub_joint` (`MultivariateDiffEntropy.lean:215`) の `h_llr_split` は n 変数版 Bayes density split。inventory §D-1a の判定: **`pi_withDensity` (joint density = ∏ marginal density) は Mathlib 不在**。2 案で詰める:
   - **案 A (2 変数 induction)**: n 変数 subadditivity を `h(Y₁..Yₙ) ≤ h(Y₁..Yₙ₋₁) + h(Yₙ)` (帰納 step) + 2 変数 subadditivity (Phase 1 結果) で組む。`MeasurableEquiv` reshape `Fin (n+1) → α ≃ᵐ (Fin n → α) × α` (`piFinSuccAbove` Phase 1 BM closure plan で実証) + `klDiv_prod_eq_add` で n 変数を 2 変数に reduce。
   - **案 B (`pi_withDensity` 自作 ~80-150 行)**: `measurePreserving_piFinSuccAbove` induction + `prod_withDensity` で `Measure.pi (μᵢ.withDensity fᵢ) = (Measure.pi μᵢ).withDensity (fun x => ∏ i, fᵢ (x i))` を genuine 構築。Mathlib PR 候補。
   Phase 0 で案 A の reduce 可否を判定 (`klDiv_prod_eq_add` (`MIChainRule.lean:254`, project genuine) が `Measure.pi` 形 vs `prod` 形の reshape を吸収できるか)。

3. **AWGN side: `IsContinuousAEPGaussian` は staged 維持 (Phase 3)**。`AWGNAchievabilityDischarge.lean:140` の predicate は continuous AEP (Shannon-McMillan-Breiman for `gaussianReal 0 σsq` i.i.d.) + n-dim typical set 体積上界 + independent-pair lower bound の **3 件 bundle**。Mathlib に continuous SMB は不在で **genuine 化は本 plan scope 外** と判定 (Mathlib 壁 type (b) = 解析の壁)。本 Phase は plan-side reflection のみ (Phase 0 で再確認、staged 維持、本 plan は subadditivity 側に集中)。

4. **段階着地**。Phase 1 (2 変数) だけ閉じれば 2 件 (`klDiv_prod_marginals_toReal_eq_sum_sub_joint` + `jointDifferentialEntropy_le_sum`、L90/L176) は genuine 化。Phase 2 (n 変数) の案 A が効けば残 2 件 (`klDiv_pi_marginals_toReal_eq_sum_sub_joint` + `jointDifferentialEntropyPi_le_sum`、L215/L280) も close。Phase 3 (AWGN staged) は plan record のみ。

**Mathlib-shape-driven 設計判断**:

- 既存定義 `jointDifferentialEntropy (μ : Measure (ℝ × ℝ)) := ∫ z, negMulLog ((μ.rnDeriv volume z).toReal) ∂volume` は `Measure.volume_eq_prod` (`rfl`) で `volume = volume.prod volume` と同視できるため、`prod_withDensity` (Mathlib 既存) が **そのまま噛む**。codomain `ℝ × ℝ` 採用 (not `EuclideanSpace ℝ (Fin 2)`) は inventory §A の Mathlib-shape 判断と整合。
- `jointDifferentialEntropyPi (μ : Measure (Fin n → ℝ))` の codomain `Fin n → ℝ` 採用 (not `EuclideanSpace`) は **product Lebesgue API** (`volume_pi`、`Measure.pi`) との直結 + `gaussianCodebook` (`AWGNAchievabilityDischarge.lean:50`) の `Measure.pi (fun _ => gaussianReal 0 σsq)` 形との **defeq** を維持する判断。
- bridge の結論形 `(klDiv μ (μ_X.prod μ_Y)).toReal = h(μ_X) + h(μ_Y) - h(joint)` は inventory §D-上 `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` (`ContChannelMIDecomp.lean:223`、手本) の 2 座標観測版 transcription。手本の honest hyp bundle (7 本) を **そのまま** 引き継いだのが現実装 (`MultivariateDiffEntropy.lean:91-116`)。Phase 1 はこの bundle の **discharge** で、bundle 形は維持。

**proof-log**: Phase 1-2 で `proof-log: yes` (density split discharge の試行錯誤を `docs/proof-logs/proof-log-multivariate-diffentropy-subadditivity.md` に記録)。Phase 0/3/V は `proof-log: no`。

**規模見積**: Phase 1 ~80-150 行 (`h_llr_split` 4-5 本 + integrability 1-2 本 discharge)、Phase 2 (案 A) ~50-100 行 / (案 B) ~150-250 行、Phase 3 0 行 (plan only)、Phase V 棚卸し ~10 行。合計 ~150-400 行。

---

## Phase 0 — 在庫確認 + suspect tag slug 整合 📋

`proof-log: no`。

### A. 在庫 (`multivariate-diffentropy-inventory.md` 24KB を入力)

inventory (2026-05-XX 起草) の判定を以下に要約。**Phase 1 着手前に再 loogle 確認**する。

#### A1. project 既存 (現状コード confirmed)

| 補題 | file:line (現在) | 引数 (要点) | conclusion (verbatim) | 状態 |
|---|---|---|---|---|
| `Common2026.Shannon.differentialEntropy` | `DifferentialEntropy.lean:42` | `(μ : Measure ℝ) : ℝ` | `:= ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume` | ✅ 1-D 既存 |
| `Common2026.Shannon.jointDifferentialEntropy` | `MultivariateDiffEntropy.lean:52` | `(μ : Measure (ℝ × ℝ)) : ℝ` | `:= ∫ z, Real.negMulLog ((μ.rnDeriv volume z).toReal) ∂volume` | ✅ 2 変数 既存 (本 plan 主役) |
| `Common2026.Shannon.jointDifferentialEntropyPi` | `MultivariateDiffEntropy.lean:58` | `{n : ℕ} (μ : Measure (Fin n → ℝ)) : ℝ` | `:= ∫ z, Real.negMulLog ((μ.rnDeriv volume z).toReal) ∂volume` | ✅ n 変数 既存 (本 plan 主役) |
| `integral_log_rnDeriv_self_eq_neg` (generic core) | `MultivariateDiffEntropy.lean:67` | `{α} [MeasurableSpace α] {μ ν} [SigmaFinite μ] [SigmaFinite ν] [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν)` | `∫ x, Real.log ((μ.rnDeriv ν x).toReal) ∂μ = -∫ x, Real.negMulLog ((μ.rnDeriv ν x).toReal) ∂ν` | ✅ genuine 既存 (本 plan core re-use) |
| `klDiv_prod_marginals_toReal_eq_sum_sub_joint` (2 変数 bridge) | `MultivariateDiffEntropy.lean:90` | `{μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ] (h_fst_ac) (h_snd_ac) (h_joint_ac) (h_llr_split) (h_int_fst) (h_int_snd) (h_int_joint) (h_int_fst_marg) (h_int_snd_marg)` (honest hyp 9 本) | `(klDiv μ ((μ.map Prod.fst).prod (μ.map Prod.snd))).toReal = differentialEntropy (μ.map Prod.fst) + differentialEntropy (μ.map Prod.snd) - jointDifferentialEntropy μ` | 🔴 `@audit:suspect(differential-entropy-plan)` (slug 不整合、本 plan の Phase 1 discharge 対象) |
| `jointDifferentialEntropy_le_sum` (2 変数 subadd) | `MultivariateDiffEntropy.lean:176` | 上と同 honest hyp 9 本 | `jointDifferentialEntropy μ ≤ differentialEntropy (μ.map Prod.fst) + differentialEntropy (μ.map Prod.snd)` | 🔴 `@audit:suspect(differential-entropy-plan)` (slug 不整合、Phase 1 discharge 対象) |
| `klDiv_pi_marginals_toReal_eq_sum_sub_joint` (n 変数 bridge) | `MultivariateDiffEntropy.lean:215` | `{n} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μ.map (fun z => z i))] (h_marg_ac) (hμ_ac) (h_joint_ac) (h_llr_split) (h_int_marg) (h_int_joint) (h_marg_id)` (honest hyp 7 本) | `(klDiv μ (Measure.pi (fun i => μ.map (fun z => z i)))).toReal = (∑ i, differentialEntropy (μ.map (fun z => z i))) - jointDifferentialEntropyPi μ` | 🔴 `@audit:suspect(differential-entropy-plan)` (slug 不整合、Phase 2 discharge 対象) |
| `jointDifferentialEntropyPi_le_sum` (n 変数 subadd) | `MultivariateDiffEntropy.lean:280` | 上と同 honest hyp 7 本 | `jointDifferentialEntropyPi μ ≤ ∑ i, differentialEntropy (μ.map (fun z => z i))` | 🔴 `@audit:suspect(differential-entropy-plan)` (slug 不整合、Phase 2 discharge 対象) |
| `klDiv_prod_eq_add` (KL prod 加法) | `MIChainRule.lean:254` | `{α' β'} [MeasurableSpace α'] [MeasurableSpace β'] (μ₁ μ₂ : Measure α') [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (ν₁ ν₂ : Measure β') [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]` | `klDiv (μ₁.prod ν₁) (μ₂.prod ν₂) = klDiv μ₁ μ₂ + klDiv ν₁ ν₂` | ✅ project genuine (Phase 1-2 で消費) |
| `klDiv_pi_eq_sum` (KL pi 加法) | `MIChainRule.lean:273` | `{n} {α' : Fin n → Type*} [∀ i, MeasurableSpace (α' i)] (μs νs : ∀ i, Measure (α' i)) [∀ i, IsProbabilityMeasure (μs i)] [∀ i, IsProbabilityMeasure (νs i)]` | `klDiv (Measure.pi μs) (Measure.pi νs) = ∑ i : Fin n, klDiv (μs i) (νs i)` | ✅ project genuine (Phase 2 消費) |

#### A2. Mathlib 既存 (loogle 2026-05-24 確認、verbatim) — Phase 1 discharge の核心

| Mathlib API | file:line | signature (verbatim) | 用途 |
|---|---|---|---|
| `MeasureTheory.prod_withDensity` | `Mathlib/MeasureTheory/Measure/WithDensity.lean:712` | `{f : α → ℝ≥0∞} {g : β → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) : (μ.withDensity f).prod (ν.withDensity g) = (μ.prod ν).withDensity (fun z ↦ f z.1 * g z.2)` | Phase 1 `h_llr_split` discharge の核 |
| `MeasureTheory.prod_withDensity₀` | `Mathlib/MeasureTheory/Measure/WithDensity.lean:705` | (AEMeasurable 版) | 上の AEMeasurable バリアント |
| `MeasureTheory.Measure.volume_eq_prod` | `Mathlib/MeasureTheory/Measure/Prod.lean:177` | `(α β) [MeasureSpace α] [MeasureSpace β] : (volume : Measure (α × β)) = (volume : Measure α).prod (volume : Measure β) := rfl` | `volume (ℝ × ℝ) = prod` (Phase 1 必須) |
| `MeasureTheory.integral_prod` | `Mathlib/MeasureTheory/Integral/Prod.lean:494` | `(f : α × β → E) (hf : Integrable f (μ.prod ν)) : ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ` | Fubini iterate (要 `[SigmaFinite ν]`) |
| `MeasureTheory.Measure.AbsolutelyContinuous.prod` | `Mathlib/MeasureTheory/Measure/Prod.lean` | `(μ₁ ≪ μ₂) (ν₁ ≪ ν₂) → μ₁.prod ν₁ ≪ μ₂.prod ν₂` | abs cont 伝播 (Phase 1 既消費 L164) |
| `MeasureTheory.Measure.rnDeriv_withDensity` | `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean` | `[SigmaFinite μ] (hf : Measurable f) : (μ.withDensity f).rnDeriv μ =ᵐ[μ] f` | density ↔ rnDeriv 同定 (Phase 1 鍵) |
| `MeasureTheory.Measure.rnDeriv_mul_rnDeriv` | `Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean` | `(hμν : μ ≪ ν) : μ.rnDeriv ν * ν.rnDeriv volume =ᵐ[volume] μ.rnDeriv volume` | rnDeriv chain rule (Phase 1 で `dμ/dν = (dμ/dvol) / (dν/dvol)` 経路) |
| `InformationTheory.toReal_klDiv_of_measure_eq` | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:164` | `(h : μ ≪ ν) (h_eq : μ univ = ν univ) : (klDiv μ ν).toReal = ∫ x, llr μ ν x ∂μ` | KL → llr 積分 (Phase 1 既消費 L131) |
| `InformationTheory.klDiv_eq_zero_iff` | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:377` | `[IsFiniteMeasure μ] [IsFiniteMeasure ν] : klDiv μ ν = 0 ↔ μ = ν` | (将来 strict 等号条件用、本 plan 主 scope 外) |
| **`pi_withDensity`** (n 変数 joint density bridge) | — | — | ❌ **Mathlib 不在** (loogle `Found 0`)。Phase 2 案 B で自作 or 案 A で迂回 |

#### A3. Phase 0 step

- [ ] **suspect tag slug 整合チェック**: `MultivariateDiffEntropy.lean` の 4 件 `@audit:suspect(differential-entropy-plan)` を `rg -nB1 '@audit:suspect' Common2026/Shannon/MultivariateDiffEntropy.lean` で列挙、本 plan の slug `multivariate-diffentropy-subadditivity-plan` に Edit で **付け替え** (Phase V step に集約)。`differential-entropy-plan.md` (DONE-HONEST-HYPS の 1-D 完成 plan) との分離を明示。
- [ ] **AWGNAchievabilityDischarge.lean:32, 117 の `@audit:suspect(differential-entropy-plan)` 言及**は **散文引用** であって tag ではないことを確認 (`@audit:` tag は `:= def` / `theorem` の docstring 末尾配置のみ規定、本 file は L139 `@audit:staged(continuous-aep-gaussian)` 1 件 + 他 staged のみで `@audit:suspect(differential-entropy-plan)` 自体は **付いていない**)。Phase 3 で再確認。
- [ ] **2 変数 induction 案 A の前提検証**: `klDiv_prod_eq_add` (`MIChainRule.lean:254`) は `(μ₁.prod ν₁) vs (μ₂.prod ν₂)` の **完全 product** 形のみ受ける。n 変数 `Measure.pi` を `(Measure.pi (Fin n)) × μ_last` に reshape する MeasurableEquiv `piFinSuccAbove` (BM closure plan §B `integral_pi_succ_eq` で実証済 measure-preserving) で対応可能か Phase 2 着手時に判定。
- [ ] **`rnDeriv_withDensity` + `prod_withDensity` chain の verbatim 確認**: Phase 1 の核心は `μ_X.withDensity f_X` + `μ_Y.withDensity f_Y` の **prod** が `(μ_X.prod μ_Y).withDensity (z ↦ f_X z.1 * f_Y z.2)` であり、その rnDeriv が `f_X z.1 * f_Y z.2` (a.e.)。log を取って `h_llr_split` の RHS と一致するか紙で先に確認。

### Done 条件 (Phase 0)

- 4 件 suspect tag の slug 付け替え準備完了 (Phase V step に列挙)、`differential-entropy-plan` との分離が docstring / plan 双方で明示可能な状態。
- Phase 1 着手前に Mathlib API 7 件 (A2 表) の signature を verbatim 確認、Phase 2 案 A/B の判定材料を inventory §D-1a と突合せ。

---

## Phase 1 — 2 変数 subadditivity bridge の honest hyp discharge ✅ (2026-05-25, commit `0fe2ad4`)

`proof-log: yes` (`docs/proof-logs/proof-log-multivariate-diffentropy-subadditivity.md`)。**実測 ~110 行** (推定 80-150 行 内)。

**着地状態**: `klDiv_prod_marginals_toReal_eq_sum_sub_joint_v2` + `jointDifferentialEntropy_le_sum_v2` (`MultivariateDiffEntropy.lean`) が 0 sorry / 0 warning で publish。`h_llr_split` (唯一の suspect 級 honest hyp、Bayes density split) を `prod_withDensity₀` + `rnDeriv_withDensity₀` + `rnDeriv_mul_rnDeriv` + `Measure.volume_eq_prod` (rfl) の chain で genuine produce。残 honest hyp は 3 abs cont + 5 integrability の **regularity bundle** のみ (1-D `differentialEntropy_le_gaussian_of_variance_le` と同性質)。命名 `_v2` 採用は旧版 (suspect 残置) を `@audit:superseded-by(<v2>)` で history record として残す方針 (Phase V で確定)。

ゴール: `klDiv_prod_marginals_toReal_eq_sum_sub_joint` (`MultivariateDiffEntropy.lean:90`) の **9 honest hyp を 2-3 本に縮減** する。具体的には `h_llr_split` (Bayes density split) を `prod_withDensity` + `rnDeriv_withDensity` で **genuine produce** し、残る integrability bundle (`h_int_*` 5 本) は最小化。abs cont (`h_fst_ac`, `h_snd_ac`, `h_joint_ac`) は regularity-style として残置可。

### Approach (Phase 内)

現状 (L90-L170) は 6 step (h_kl / h_split / h_add / h_fst / h_snd / h_jt) で `h_llr_split` を 1 行 (L134-L137 `integral_congr_ae`) で受けるが、`h_llr_split` の **中身** は `μ_X.withDensity f_X`-flavour と `μ` の rnDeriv の比、すなわち:

```
llr μ (μ_X.prod μ_Y) z = log ((μ.rnDeriv (μ_X.prod μ_Y) z).toReal)
  =ᵐ[μ] log ((μ.rnDeriv volume z).toReal)
        - log (((μ_X).rnDeriv volume z.1).toReal)
        - log (((μ_Y).rnDeriv volume z.2).toReal)
```

これを Mathlib `prod_withDensity` + `rnDeriv_withDensity` + `rnDeriv_mul_rnDeriv` の連鎖で **genuine 化**する step:

1. `μ_X.prod μ_Y = (volume.withDensity (fst_density)).prod (volume.withDensity (snd_density))` (`μ_X ≪ volume` から `Measure.eq_withDensity_rnDeriv` 系で書き換え)。
2. `prod_withDensity` で `= (volume.prod volume).withDensity (z ↦ fst_density z.1 * snd_density z.2)`。
3. `Measure.volume_eq_prod` (rfl) で `volume.prod volume = (volume : Measure (ℝ × ℝ))`。
4. `μ.rnDeriv (μ_X.prod μ_Y)` を `Measure.rnDeriv_mul_rnDeriv` で `(μ.rnDeriv volume) / (μ_X.prod μ_Y).rnDeriv volume = (μ.rnDeriv volume) / (fst_density z.1 * snd_density z.2)`。
5. `log` を取って `Real.log_div` で `log (μ rnDeriv) - log (fst_density z.1) - log (snd_density z.2)` の `=ᵐ[μ]` 形に。
6. ここで `fst_density z.1 = (μ_X.rnDeriv volume z.1)` (rnDeriv の規約) で `h_llr_split` の RHS と一致。

### step

- [ ] **§1.1 `density_factorize_prod_marginals`**: `(μ.map Prod.fst).prod (μ.map Prod.snd)` の density が `μ_X` 側 density × `μ_Y` 側 density で因子化されることを `prod_withDensity` で genuine 構築。signature:
  ```lean
  theorem density_factorize_prod_marginals
      {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
      (h_fst_ac : μ.map Prod.fst ≪ volume) (h_snd_ac : μ.map Prod.snd ≪ volume) :
      (μ.map Prod.fst).prod (μ.map Prod.snd)
        = volume.withDensity (fun z => (μ.map Prod.fst).rnDeriv volume z.1
                                          * (μ.map Prod.snd).rnDeriv volume z.2)
  ```
  本体: `eq_withDensity_rnDeriv` (Mathlib) で `μ_X = volume.withDensity (μ_X.rnDeriv volume)` を取り、`prod_withDensity` で展開、`Measure.volume_eq_prod` (rfl) で `volume.prod volume = (volume : Measure (ℝ × ℝ))` を結合。
- [ ] **§1.2 `llr_split_from_density_factorize`**: §1.1 の結論を使い `h_llr_split` を produce。`Measure.rnDeriv_withDensity` + `Measure.rnDeriv_mul_rnDeriv` + `Real.log_mul` (要正性確認、density は a.e. 正) で `log` 形に。最終 statement:
  ```lean
  theorem llr_split_from_density_factorize
      {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
      (h_fst_ac : μ.map Prod.fst ≪ volume) (h_snd_ac : μ.map Prod.snd ≪ volume)
      (h_joint_ac : μ ≪ (μ.map Prod.fst).prod (μ.map Prod.snd)) :
      (fun z => llr μ ((μ.map Prod.fst).prod (μ.map Prod.snd)) z)
        =ᵐ[μ] (fun z => Real.log ((μ.rnDeriv volume z).toReal)
                          - Real.log (((μ.map Prod.fst).rnDeriv volume z.1).toReal)
                          - Real.log (((μ.map Prod.snd).rnDeriv volume z.2).toReal))
  ```
  これで現状 `klDiv_prod_marginals_toReal_eq_sum_sub_joint` の `h_llr_split` 引数 (4-5 行 hyp) が **不要に**。
- [ ] **§1.3 marginal id 自動化**: `h_int_fst_marg` / `h_int_snd_marg` (marginal-side integrability 2 本) も `integral_map` (Mathlib) の前提を整えるため `Measurable.aestronglyMeasurable` で自動 derive 可能。残るのは joint-side integrability `h_int_fst / h_int_snd / h_int_joint` 3 本のみで、これらは **本質的に Bochner 慣習の regularity** (Gaussian / log-concave 規定で充足、現実装で利用される `differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:510`) の `h_var_int` / `h_ent_int` と同性質)。
- [ ] **§1.4 `klDiv_prod_marginals_toReal_eq_sum_sub_joint_v2`** (genuine discharge 版): §1.2 の `llr_split_from_density_factorize` を使い、`klDiv_prod_marginals_toReal_eq_sum_sub_joint` を `h_llr_split` 引数なしで restate。本体は現実装 (L120-L170) を `llr_split_from_density_factorize` で 1 行置換するだけ。
- [ ] **§1.5 `jointDifferentialEntropy_le_sum_v2`**: §1.4 を使い、`jointDifferentialEntropy_le_sum` の `h_llr_split` 引数を撤去した restate (`ENNReal.toReal_nonneg` + bridge で `linarith`)。

### 撤退条件

- **`Real.log_mul` の正性前提が a.e. でしか効かない場合**: `μ.rnDeriv volume z` が `μ ≪ volume` の元では a.e.-finite だが、`(μ_X.rnDeriv volume z.1) * (μ_Y.rnDeriv volume z.2)` の log split は `f g > 0 a.e.` を要求。density が **どこで 0 になるか**で `=ᵐ[μ]` の filter 条件 (`μ`-a.e.) に頼る形になる。**>200 行**で行き詰まる場合は §1.2 の最終 `=ᵐ[μ]` を honest hyp として **残置** (現状から進歩なしに見えるが、`h_llr_split` の RHS が `Real.log` 表現でなく density 表現に **swap** されていれば前進)。
- **`prod_withDensity` の前提 `Measurable f` が strict すぎて `AEMeasurable` 版 `prod_withDensity₀` でも回避不可な場合**: `μ.rnDeriv volume` が `Measurable` で `AEMeasurable` でないことは Mathlib `Measure.measurable_rnDeriv` で保証 → 発動回避見込み。

### Done 条件

- `klDiv_prod_marginals_toReal_eq_sum_sub_joint_v2` (§1.4) + `jointDifferentialEntropy_le_sum_v2` (§1.5) が 0 sorry、honest hyp は abs cont 3 + joint-side integrability 3 のみ (`h_llr_split` 撤去)。
- **段階着地点 1: 2 変数 subadditivity が `h_llr_split` 不要に genuine 化**。

---

## Phase 2 — n 変数 subadditivity 完全 genuine 化 🔄 **re-opened 2026-05-29**

> **対象 file**: `Common2026/Draft/Shannon/MultivariateDiffEntropy.lean` (Draft 配下に移動済、計画書旧本文の `Common2026/Shannon/` 行番号は drift)。
>
> **対象 declaration (verbatim 行確認済 2026-05-29)**:
> - bridge `klDiv_pi_marginals_toReal_eq_sum_sub_joint` (`MultivariateDiffEntropy.lean:242`)
> - subadd `jointDifferentialEntropyPi_le_sum` (`MultivariateDiffEntropy.lean:257`、`@[entry_point]`)
>
> **現状コード (2026-05-29 verbatim 確認、前回 plan 文の「honest hyp 温存」記述から drift)**: 両 declaration は既に **honest hyp 形ではなく sorry-routed**。regularity hyp は `_h_marg_ac` / `_hμ_ac` / `_h_joint_ac` の underscore で残置 (load-bearing predicate ではない、honest)、body は丸ごと `sorry` + `@residual(plan:multivariate-diffentropy-subadditivity-plan)`。前回 Wave 3 の「honest hyp 温存」は小 cluster sorry-migration (file docstring §"Phase 2 — withdrawal note" L522-527) で既に sorry-routed に移行済。**本 re-open は sorry-routed → genuine への前進であって、honest hyp への後退ではない**。

### 前回 withdrawal の誤診 (2026-05-29 再調査で確定)

前回 (Wave 3) の停止理由「generic `withDensity_map` が Mathlib 不在 → 案 A 不能」は **gap を誤診**していた:

- generic `withDensity_map` (`(μ.withDensity g).map e = (μ.map e).withDensity (g ∘ e.symm)`) が Mathlib 不在なのは事実 (5 命名候補 + 結論パターン `Found 0` で authoritative 確認、inventory §1)。しかし前回は **「不在 = 自作不能」と誤って扱い** withdrawal した。実際は **自作未着手**。
- rnDeriv 特化版 `MeasurableEmbedding.map_withDensity_rnDeriv` (`Mathlib/.../RadonNikodym.lean:537`) が **5 行の脱特化テンプレート**を提供 (`ext` → `map_apply` → `withDensity_apply` ×2 → `setLIntegral_map` → 最後の congr)。generic 版は最後の `rnDeriv_map` step を `simp [e.symm_apply_apply]` で潰すだけなので **rnDeriv 版より短くなる見込み** (inventory §1 判定)。
- 自作部品 (`Measure.ext` / `setLIntegral_map` / `withDensity_apply` / `MeasurableEquiv.map_apply`) + reshape 部品 (`MeasurableEquiv.piFinSuccAbove` / `measurePreserving_piFinSuccAbove` / `MeasurableEquiv.funUnique`) は全て verbatim 在庫 (inventory §2 / §5)。

**inventory 2026-05-29 ゲート判定**: closeable = (b) 自作 helper ~15-25 行 + closure 全体 ~150-250 行 (撤退境界 250 行内)。真の `@residual(wall:...)` 対象は **ゼロ** (現状 `@residual(plan:...)` 分類は honest、helper 自作 1 本で道が開く)。代替路 (rnDeriv-of-product 直接) は `rnDeriv_prod` / `rnDeriv_pi` 双方不在で却下 (inventory §4)。

### Approach (Phase 2 re-open の shape)

「helper-first + structural-bridge 分離 + density-split を独立補題に切出し」のハイブリッド。**段階着地を 2 点設ける** (Phase 2a / 2b)。

proof-pivot-advisor の構造的洞察 (2026-05-29) を反映:

- **2 変数 bridge `klDiv_prod_marginals_toReal_eq_sum_sub_joint` (`MultivariateDiffEntropy.lean:113`) の本体は `prod_withDensity` を使っていない**。verbatim 確認 (L143-193): KL を `toReal_klDiv_of_measure_eq` (L154) で `∫ llr ∂μ` に開き、honest hyp `h_llr_split` (L120-125) で llr を 3 本の log-density に分解 (L157-160 `h_split`)、各項を `integral_log_rnDeriv_self_eq_neg` (`:86`、genuine) + `integral_map` で marginal entropy に変換 (L171-190 `h_fst` / `h_snd` / `h_jt`)。`prod_withDensity` は後付け `_v2` (`prod_marginals_eq_volume_withDensity:285` + `llr_split_from_density_factorize:313`) が `h_llr_split` を discharge する箇所だけで使われる。
- → **n 変数 bridge の structural 部分 (~60-90 行) は density split 抜きで genuine 化可能**。真の壁は n 変数 density split (`h_llr_split` 相当) 1 点に局所化する。
- `klDiv_pi_eq_sum` (`MIChainRule.lean:273`、genuine) は第 1 引数が `Measure.pi` 形を要求 → joint μ (product でない) には **直接使えない**。subadditivity は `KL(joint ‖ ∏marginal) ≥ 0` の構造なので、bridge は per-marginal 引き戻し (`integral_log_rnDeriv_self_eq_neg` を `μ.map (· i)` 各々に適用 + `integral_map`) が正しいルート。

#### Phase 2a — structural bridge を genuine 化 (density split を独立 sorry 補題に切出し)

1. **n 変数 density split を独立補題に切出し** `llr_split_from_density_factorize_pi` (最初は body `sorry` + `@residual`)。
2. **bridge `klDiv_pi_marginals_toReal_eq_sum_sub_joint` を 2 変数版と同型骨格で genuine に書く**。2 変数本体 (L143-193) の 6 step 構造を `Fin n → ℝ` carrier + `Finset.sum` 一般化に transcribe: `toReal_klDiv_of_measure_eq` (KL → llr 積分) + 上記 split 補題 (llr → log-density sum) + `Finset.sum` 版の `integral_sub` 連鎖 + `integral_log_rnDeriv_self_eq_neg` + `integral_map` (Prod.fst/snd → `(· i)`, 2 項 → `∑ i`)。
3. **`jointDifferentialEntropyPi_le_sum` を genuine 化**: bridge + `ENNReal.toReal_nonneg` の `linarith` (2 変数版 `jointDifferentialEntropy_le_sum:203` 本体 L228-233 と同型)。split 補題が sorry でも bridge/subadd の structural は genuine。
- → **段階着地点 A: subadd の sorry が density split 1 点に集約、bridge/subadd は structural genuine**。残り sorry の classification は `@residual(plan:multivariate-diffentropy-subadditivity-plan)` を density-split 補題に明記。

**honesty 警告 (厳守)**: density split を `h_llr_split` honest hyp として bridge 引数に **戻すのは禁止** (load-bearing hyp = tier 5 = 現 sorry-routed より strictly less honest、CLAUDE.md「検証の誠実性」)。必ず独立補題 `llr_split_from_density_factorize_pi` の sorry body に閉じ込める。bridge / subadd の引数は regularity (`≪` / `Integrable`) のみ。

##### 補題 signature (verbatim、着手時はこの形で skeleton 化)

```lean
-- §2a.1 — n 変数 density split を独立補題に切出し (最初は sorry)
/-- **Genuine Bayes density split for the n-variable joint (a.e.[μ]).**
@residual(plan:multivariate-diffentropy-subadditivity-plan) -/
theorem llr_split_from_density_factorize_pi
    {n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (μ.map (fun z => z i))]
    (h_marg_ac : ∀ i, (μ.map (fun z => z i)) ≪ volume)
    (hμ_ac : μ ≪ (volume : Measure (Fin n → ℝ)))
    (h_joint_ac : μ ≪ Measure.pi (fun i => μ.map (fun z => z i))) :
    (fun z => llr μ (Measure.pi (fun i => μ.map (fun z => z i))) z)
      =ᵐ[μ]
    (fun z => Real.log ((μ.rnDeriv volume z).toReal)
                - ∑ i, Real.log (((μ.map (fun z => z i)).rnDeriv volume (z i)).toReal)) := by
  sorry
```

> **注意 (verbatim 確認した 2 変数版との対応)**: 2 変数版 `llr_split_from_density_factorize` (`:313`) の結論 (L318-322) は marginal 項を `z.1` / `z.2` で個別に subtract する形 (`... - log(μX rnDeriv (z.1)) - log(μY rnDeriv (z.2))`)。n 変数版はこれを `- ∑ i, log(μ.map (· i) rnDeriv (z i))` の `Finset.sum` に一般化。bridge 結論 (`klDiv_pi_marginals_toReal_eq_sum_sub_joint:248-249`) も `∑ i, differentialEntropy (μ.map (fun z => z i))` の sum 形なので整合。

Phase 2a 完了後の bridge / subadd は引数から `h_llr_split` を削除し (もともと sorry-routed なので削除不要、body を上記 split 補題呼び出し + structural assembly で埋める)、`sorry` を 0 にする (split 補題が sorry を吸収)。**ただし bridge / subadd 自身に残る sorry は 0、`llr_split_from_density_factorize_pi` の 1 点のみが sorry**。

#### Phase 2b — density split を genuine discharge (= 完全 closure)

1. **generic `withDensity_map` helper を自作** (~15-25 行、`MeasurableEmbedding.map_withDensity_rnDeriv` (`RadonNikodym.lean:537`) の 5 行証明を density 一般に脱特化)。signature (inventory §"着手 skeleton" L422-425):
   ```lean
   /-- generic `withDensity_map` (Mathlib 不在、rnDeriv 版を脱特化)。 -/
   theorem withDensity_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
       {μ : Measure α} (e : α ≃ᵐ β) {g : α → ℝ≥0∞} (hg : Measurable g) :
       (μ.withDensity g).map e = (μ.map e).withDensity (g ∘ e.symm) := by
     sorry  -- ext + e.map_apply + withDensity_apply ×2 + setLIntegral_map + symm_apply_apply
   ```
   > 落とし穴 (inventory §"自作が必要な要素" 1.): `g ∘ e.symm` の可測性 `hg.comp e.symm.measurable` を `setLIntegral_map` に渡す。`e.symm (e x)` 簡約は `MeasurableEquiv.symm_apply_apply` (defeq でなければ `simp`)。`SigmaFinite` は generic density 版では落とせる見込み (rnDeriv 版が要求するのは `rnDeriv_map` step のため、generic 版はその step を `symm_apply_apply` で回避) — 着手時要確認。
2. **`pi_withDensity` を genuine 構築** (`Measure.pi (fun i => μᵢ.withDensity fᵢ) = (Measure.pi μᵢ).withDensity (fun x => ∏ i, fᵢ (x i))`) を `measurePreserving_piFinSuccAbove` (`Pi.lean:802`) induction + `prod_withDensity` (`WithDensity.lean:712`) + helper #1 で genuine 構築。
   > 注意点 (inventory §"主要前提条件ボックス"): `Measure.pi` を `(μ i).prod (Measure.pi rest)` に reshape した後、4-measure 前提を持つ補題に渡すなら reshape 後の `Measure.pi rest` への `IsProbabilityMeasure` instance 供給 (`MeasureTheory.isProbabilityMeasure_pi` / `Measure.isProbabilityMeasure_map` pattern) が helper とは別に **1 配線必要**。
3. **`llr_split_from_density_factorize_pi` の sorry を discharge** (2 変数版 `llr_split_from_density_factorize:313` と並行構造: `prod_marginals_eq_volume_withDensity` → `pi_withDensity`、`rnDeriv_mul_rnDeriv` + `Real.log_mul` の chain + `Finset.sum` 版 log split)。
- → **段階着地点 B: n 変数 subadditivity 完全 genuine (0 sorry / 0 residual)**。bridge / subadd / split 補題 / helper の全てが 0 sorry。

### step

- [ ] **§2a.1** `llr_split_from_density_factorize_pi` を上記 signature で skeleton 化 (body `sorry` + `@residual(plan:multivariate-diffentropy-subadditivity-plan)`)。LSP で type-check (sorry warning のみ)。
- [ ] **§2a.2** bridge `klDiv_pi_marginals_toReal_eq_sum_sub_joint` (`:242`) を 2 変数本体 (L143-193) 同型骨格で genuine に埋める。`toReal_klDiv_of_measure_eq` + `llr_split_from_density_factorize_pi` + `Finset.sum` 版 `integral_sub` + `integral_log_rnDeriv_self_eq_neg` + `integral_map`。bridge 自身に残る sorry = 0。
- [ ] **§2a.3** subadd `jointDifferentialEntropyPi_le_sum` (`:257`) を bridge + `ENNReal.toReal_nonneg` の `linarith` で genuine に埋める (2 変数版 L228-233 同型)。subadd 自身に残る sorry = 0。**段階着地点 A 確定**。
- [ ] **§2b.1** `withDensity_map_equiv` helper を上記 signature で skeleton → genuine 化 (~15-25 行)。
- [ ] **§2b.2** `pi_withDensity` を `measurePreserving_piFinSuccAbove` induction + `prod_withDensity` + helper #1 で genuine 構築。reshape 後 `Measure.pi rest` への `IsProbabilityMeasure` 配線も入れる。
- [ ] **§2b.3** §2b.2 を使い `llr_split_from_density_factorize_pi` の sorry を discharge。**段階着地点 B 確定 (0 sorry / 0 residual)**。

### 撤退条件 (Phase 2 re-open)

- **Phase 2b が >250 行 or 新たな Mathlib 壁に当たる** → 段階着地点 A (structural genuine + density split 1 点 sorry) で stop。これは現状 (subadd 丸ごと sorry) より strictly honest な前進 (sorry が bridge/subadd 全体から density split 1 補題に局所化)。`llr_split_from_density_factorize_pi` の body `sorry` + `@residual(plan:multivariate-diffentropy-subadditivity-plan)` を残置。
- **helper 自作中 (§2b.1) に `setLIntegral_map` / `MeasurableEquiv.map_apply` の前提が合わない** → inventory §1 / §2 の紙スケッチ (`withDensity_map_equiv` の `ext` → `withDensity_apply` → `setLIntegral_map` → `symm_apply_apply` 経路) を参照。それでも詰まれば inventory §"撤退ラインへの距離" [G-1] に従い helper を共有 sorry 補題 (`withDensity_map_equiv := by sorry` + `@residual(wall:withdensity-map-equiv)`) に切り出し、induction 本体だけ genuine 化。これでも段階着地点 A は確保。
- **§2a.2 で `Finset.sum` 版 `integral_sub` 連鎖 (2 変数の `h_add` L162-169 の n 項一般化) が予想外に重い** → `Finset.sum_sub_distrib` / `integral_finset_sum` (各 log-density 項の `Integrable` 前提が必要) で組む。各項 integrability は regularity hyp として bridge 引数に追加 (2 変数版 `h_int_fst` 等と同性質、load-bearing でない precondition なので OK)。
- **`sorry` は honest に残す**。`:True` placeholder / 結論型≡仮説型 / 退化定義悪用 / `h_llr_split` を honest hyp に戻す bundling は禁止 (CLAUDE.md「検証の誠実性」)。

### Done 条件 (Phase 2 re-open)

- **Phase 2a (段階着地点 A)** — *type-check done*: `lake env lean Common2026/Draft/Shannon/MultivariateDiffEntropy.lean` が 0 errors。bridge `klDiv_pi_marginals_toReal_eq_sum_sub_joint` + subadd `jointDifferentialEntropyPi_le_sum` が自身に 0 sorry (structural genuine)、唯一の sorry は `llr_split_from_density_factorize_pi` の body 1 点 + `@residual(plan:multivariate-diffentropy-subadditivity-plan)`。bridge / subadd / split 補題の引数は regularity (`≪` / `Integrable` / instance) のみ、load-bearing predicate なし。
- **Phase 2b (段階着地点 B)** — *proof done*: 上記に加えて `MultivariateDiffEntropy.lean` の n 変数 declaration 群 (bridge / subadd / split 補題 / `withDensity_map_equiv` / `pi_withDensity`) が **0 sorry / 0 @residual**。独立 honesty auditor が pass 判定すれば `@audit:ok` 付与 (helper `withDensity_map_equiv` の generic 化が honest = 「Mathlib に名前が無いだけ」の選択案件で wall 化不要であることを含めて検証)。

### 規模見積り (Phase 2 re-open)

- Phase 2a: split 補題 skeleton ~10 行 (sorry) + bridge genuine ~60-90 行 + subadd genuine ~5-10 行 = **~75-110 行** (段階着地点 A まで)。
- Phase 2b: helper `withDensity_map_equiv` ~15-25 行 + `pi_withDensity` induction ~50-100 行 + split 補題 discharge ~30-50 行 = **~95-175 行** (段階着地点 B まで、累計 ~150-250 行 = inventory ゲート判定と整合)。

---

以下は **2026-05-25 (Wave 3) の honest withdrawal 記録** (誤診と判明、再開時の参照用に保持)。

### Honest withdrawal — 2026-05-25 (Wave 3, commit `0fe2ad4`)

**判定**: Mathlib gap により本 plan scope 外と判定、honest withdrawal。`klDiv_pi_marginals_toReal_eq_sum_sub_joint` (`MultivariateDiffEntropy.lean:215`) + `jointDifferentialEntropyPi_le_sum` (L280) は **honest hyp 温存** (撤退ライン §"案 A / 案 B 双方で行き詰まる (>250 行)" 適用)、`@audit:suspect(multivariate-diffentropy-subadditivity-plan)` slug を本 plan 自身に向けて maintain (residual discharge target として再開可能性を残す)。

**Mathlib gap (block 元)**: 案 A (2 変数 induction) を ~250 行まで試行した結果、**generic `withDensity_map`**:
```
(μ.withDensity g).map e = (μ.map e).withDensity (g ∘ e.symm)
                          (e : α ≃ᵐ β   measurable equivalence、g : α → ℝ≥0∞ measurable)
```
が Mathlib 不在と判明 (rnDeriv 特化版 `MeasurableEmbedding.map_withDensity_rnDeriv` のみ存在)。`MeasurableEquiv.piFinSuccAbove` で `Measure.pi` を `ℝ × Measure.pi` に reshape する各 step で本 lemma が要求され、自作 ~10 行 helper + 4 件の周辺 friction (詳細 proof-log §"Frictions hit") の累計が >250 行に達する見込み。`pi_withDensity` (案 B) も同 gap を内包するため案 B fall-back では不解消 (proof-log §"meta — observations" の plan 修正提案)。

**確定済段階着地**: Phase 1 の 2 変数 genuine 化は維持。本 plan は **2 変数で stop**、n 変数は別 sub-plan / Mathlib PR 経由で再開。

**再開条件 (どちらか)**:
1. **Mathlib PR `Measure.map_withDensity` (or `MeasurableEquiv.map_withDensity`) merge** — proof-log §"meta — observations" の up-stream 候補。`Measure.ext` + `MeasurableEquiv.lintegral_map` で ~10 行で証明可能と評価済。PR は未提出 (2026-05-25)、将来 task。
2. **自作 ~80-150 行 bridge** — Mathlib PR を待たず本 plan 内で generic `withDensity_map` を helper として自作。`measurePreserving_piFinSuccAbove` (BM closure plan §B で実証済) を併用すれば残 4 件 friction も連動解消の見込み (proof-log §"Frictions hit" の `(1)` `(2)` `(3)` `(5)` は本 helper があれば mechanical)。

**proof-log 参照**: 試行詳細は `docs/proof-logs/proof-log-multivariate-diffentropy-subadditivity.md` §"Phase 2 — n-variable case (withdrawal)" を参照 (案 A スケッチ ~250 行 + 5 friction の優先順位 + Mathlib gap 同定の経緯)。

---

以下は **撤退前の original 計画** (再開時の参照用に保持)。

`proof-log: yes`。**推定 ~50-250 行** (案 A / 案 B で大幅変動)。

ゴール: `klDiv_pi_marginals_toReal_eq_sum_sub_joint` (`MultivariateDiffEntropy.lean:215`) の `h_llr_split` (n 変数 Bayes density split) を **2 案のいずれか**で discharge。

### Approach 案 A (2 変数 induction, 推奨)

`h(Y₁..Yₙ) ≤ ∑ᵢ h(Yᵢ)` を `Nat.rec` で組む:

- **base** `n = 1`: `Fin 1 → ℝ ≃ᵐ ℝ` (`MeasurableEquiv.funUnique`、BM closure plan §C' L154 で実証)。
- **step** `n → n+1`: `Fin (n+1) → ℝ ≃ᵐ ℝ × (Fin n → ℝ)` (`MeasurableEquiv.piFinSuccAbove 0`、BM closure plan §B `integral_pi_succ_eq` の reshape と同じ choice)。slice 視点で `h(Y₁..Yₙ₊₁) ≤ h(Y₁) + h(Y₂..Yₙ₊₁) ≤ h(Y₁) + ∑ᵢ₌₂..ₙ₊₁ h(Yᵢ)` の 2 段、内側は Phase 1 (2 変数) を `Fin n → ℝ` 側 carrier に適用、外側は帰納仮定。

### Approach 案 B (`pi_withDensity` 自作, 重い)

Mathlib 不在の `pi_withDensity`:

```
Measure.pi (fun i => μᵢ.withDensity fᵢ)
  = (Measure.pi μᵢ).withDensity (fun x => ∏ i, fᵢ (x i))
```

を `measurePreserving_piFinSuccAbove` induction + `prod_withDensity` で自作 (~80-150 行)。これが取れれば Phase 1 と完全並行に n 変数 `llr_split_from_density_factorize_pi` を genuine 構築可能。**Mathlib 上流 PR 候補**。

### Phase 0 判定 (案 A vs 案 B)

inventory §D-1a の judgement: 案 A 推奨 (案 B は `Measurable f` 一様前提 + induction 中の measurability 配線が重く、>100 行 rabbit hole リスク)。Phase 0 で `klDiv_prod_eq_add` (`MIChainRule.lean:254`) が 2 変数 step の核として使えるか + `Measure.pi` を `μ_last × Measure.pi (rest)` に reshape する `MeasurableEquiv` が `piFinSuccAbove` (BM closure plan §B で実証) で済むかを再確認。

### step

- [ ] **§2.0 案決定**: Phase 0 step で案 A 採用判定。決定論的 fall-back として案 B も用意。
- [ ] **§2.1 (案 A) `subadditivity_step`**: `h(Y₁..Yₙ₊₁) ≤ h(Y₁) + h(Y₂..Yₙ₊₁)` を Phase 1 (2 変数) + `MeasurableEquiv.piFinSuccAbove 0` reshape で genuine 化。signature:
  ```lean
  theorem subadditivity_step
      {n : ℕ} {μ : Measure (Fin (n+1) → ℝ)} [IsProbabilityMeasure μ]
      (honest_hyps : ...) :  -- Phase 1 同型 honest bundle
      jointDifferentialEntropyPi μ
        ≤ differentialEntropy (μ.map (· 0))
          + jointDifferentialEntropyPi (μ.map (fun x i => x i.succ))
  ```
- [ ] **§2.2 (案 A) `jointDifferentialEntropyPi_le_sum_v2`** (帰納本体): `Nat.rec` で base (`n=1`) + step (§2.1) を組み合わせる。残 honest hyp は Phase 1 と同型の **regularity bundle** のみ (n 個の `μ.map (· i) ≪ volume` + joint abs cont + joint integrability)。
- [ ] **§2.3 (案 B fall-back) `pi_withDensity` 自作**: `measurePreserving_piFinSuccAbove` (BM closure plan で実証済) + `prod_withDensity` induction。`Mathlib.MeasureTheory.Measure.WithDensity` への PR 候補として up-streaming も判断ログに記録。

### 撤退条件

- **案 A の `MeasurableEquiv.piFinSuccAbove 0` で `Measure.pi (μ.map (· i))` を `(μ.map (· 0)) × Measure.pi (μ.map (· i.succ))` に reshape する step が `klDiv_prod_eq_add` の前提 (`IsProbabilityMeasure`) を欠く場合**: 各 marginal の `IsProbabilityMeasure` instance は `Measure.isProbabilityMeasure_map` で自動 derive 可能 (現実装 L123-L124 で 2 変数版を実証)。発動回避見込み。
- **>250 行で案 A が行き詰まる場合**: 案 B (`pi_withDensity` 自作) に切替。
- **案 B も >250 行で行き詰まる場合**: n 変数 subadditivity を `pi_withDensity` の **honest hyp 化** で温存 (現状から進歩なし、撤退ライン D-1a)。**ただし 2 変数版 (Phase 1) は genuine 化済なので段階着地点 1 は確保**。

### Done 条件

- `jointDifferentialEntropyPi_le_sum_v2` (§2.2) が 0 sorry、honest hyp は regularity bundle (abs cont n+1 + joint integrability) のみ (`h_llr_split` 撤去)。
- **段階着地点 2: n 変数 subadditivity も `h_llr_split` 不要に genuine 化**。

---

## Phase 3 — AWGN `IsContinuousAEPGaussian` plan-side reflection 📋

`proof-log: no`。**0 行実装** (plan record のみ)。

ゴール: `AWGNAchievabilityDischarge.lean:140` の `IsContinuousAEPGaussian P N` (`@audit:staged(continuous-aep-gaussian)`) について **本 plan が discharge しない**ことを明示し、Mathlib 壁 (continuous SMB / n-dim differentialEntropy) を staged 維持の理由として記録。

### 判定根拠

`IsContinuousAEPGaussian` の bundle 3 件:
1. **joint typical probability → 1**: 連続版 AEP (Shannon-McMillan-Breiman) を Gaussian i.i.d. に適用、Mathlib 不在 (`smb-continuous`)。
2. **typical-set 体積上界 `vol(Aε^{(n)}) ≤ exp(n(h+ε))`**: n-dim `jointDifferentialEntropyPi` で書かれているが、`vol(typical set)` の上界は連続 AEP の本質的内容。
3. **independent-pair upper bound** `P[(X', Y) ∈ Aε] ≤ exp(-n(I-3ε))`: KL form (Option γ, `AWGNAchievabilityDischarge.lean:32` 判断 #3) で書かれており本 plan の `multivariate-diffentropy-subadditivity` slug を **回避** している (`@audit:suspect(differential-entropy-plan)` の散文引用は Option β 経路の説明、tag そのものは付いていない)。

3 件はいずれも **本 plan の subadditivity discharge の対象外** であり、AWGN side の `@audit:staged(continuous-aep-gaussian)` 2 件 (`AWGNAchievabilityDischarge.lean:137, 139`) は **staged 維持**。

### step

- [ ] **L32 / L117 散文引用の再確認**: `rg -nB1 'differential-entropy-plan' Common2026/Shannon/AWGNAchievabilityDischarge.lean` で 2 件が **散文 docstring 引用** (`@audit:` tag ではない) であることを確認。本 plan の slug `multivariate-diffentropy-subadditivity-plan` への参照書き換えは **不要** (散文の文脈は Option β 経路の説明であって、本 plan の slug 直結ではない)。
- [ ] **判断ログに staged 維持を記録**: 本 sub-plan が `IsContinuousAEPGaussian` を discharge しないことを判断ログに明記、AWGN side の sibling plan (`awgn-achievability-typicality-plan.md`) からのリンクは AWGN 側で管理。

### 撤退条件

- (該当なし、plan record のみ)

### Done 条件

- L32 / L117 の散文引用が tag ではないことを確認、本 plan は `IsContinuousAEPGaussian` を **discharge しない**ことを判断ログに記録。

---

## Phase V — clean + slug 付け替え 📋

`proof-log: no`。

- [ ] `lake env lean Common2026/Shannon/MultivariateDiffEntropy.lean` silent (0 error / 0 sorry / 最小 warning) — 実装時に確認。
- [ ] **4 件 `@audit:suspect` の slug 付け替え** (本 plan の主 plumbing 成果):
  - `MultivariateDiffEntropy.lean:89` (`klDiv_prod_marginals_toReal_eq_sum_sub_joint`) — `@audit:suspect(differential-entropy-plan)` → Phase 1 完了で **撤去** or **`@audit:closed-by-successor(multivariate-diffentropy-subadditivity-plan)`** (`_v2` で genuine 化済の場合)。
  - `MultivariateDiffEntropy.lean:175` (`jointDifferentialEntropy_le_sum`) — 同上。
  - `MultivariateDiffEntropy.lean:214` (`klDiv_pi_marginals_toReal_eq_sum_sub_joint`) — Phase 2 完了で同様。
  - `MultivariateDiffEntropy.lean:279` (`jointDifferentialEntropyPi_le_sum`) — 同上。
  撤回判定: 完全 discharge なら tag 削除 + docstring 修正、honest hyp 残置 (regularity bundle 形) なら `@audit:suspect(multivariate-diffentropy-subadditivity-plan)` に slug 更新 (本 plan 自身の slug)。
- [ ] **AWGN side `@audit:staged(continuous-aep-gaussian)` 2 件は touch せず** (Phase 3 判定)。
- [ ] **残存 honest hypothesis 棚卸し**: Phase 1-2 後に残る hyp (abs cont 系 + integrability 系) を proof-log に列挙、各々 `:= True` でなく実 `Prop` 命題 (`AbsolutelyContinuous` / `Integrable` 等) であることを確認。
- [ ] 親 family の moonshot がある場合は末尾にポインタ追記 (現状本 plan は family なし、近接 plan からのリンクは A1 で記載済)。

### Done 条件

- 4 件 suspect tag が **付け替え or 撤去** され、`@audit:suspect(differential-entropy-plan)` slug は 0 件 (`differential-entropy-plan.md` 1-D plan は無関係であることがコード SoT で明示)。
- 残存 honest hyp が regularity bundle のみで `:= True` placeholder 不在。

---

## 次の一手 (2026-05-29 時点、Phase 2 re-open)

- **Phase 2 を re-open** (前回 Wave 3 withdrawal は gap を誤診)。`Common2026/Draft/Shannon/MultivariateDiffEntropy.lean` の n 変数 sorry 2 点 (`klDiv_pi_marginals_toReal_eq_sum_sub_joint:242` + `jointDifferentialEntropyPi_le_sum:257`) を genuine 化する。
- **着手は §2a.1 から**: `llr_split_from_density_factorize_pi` を skeleton 化 (sorry) → §2a.2 bridge genuine → §2a.3 subadd genuine で **段階着地点 A** (structural genuine + density split 1 点 sorry)。ここまでで現状 (丸ごと sorry) より strictly honest な前進。
- **段階着地点 A の後 §2b** で `withDensity_map_equiv` helper 自作 → `pi_withDensity` → split 補題 discharge = **段階着地点 B** (0 sorry / 0 residual)。
- **lean-implementer brief で渡すべき verbatim 値**: 対象 file = `Common2026/Draft/Shannon/MultivariateDiffEntropy.lean` (Draft 配下、`Common2026/Shannon/` ではない)、template = `MeasurableEmbedding.map_withDensity_rnDeriv` (`Mathlib/.../RadonNikodym.lean:537`、5 行証明)、2 変数 同型骨格 = `klDiv_prod_marginals_toReal_eq_sum_sub_joint:113-193` (6 step) + `llr_split_from_density_factorize:313`。
- **新規 sorry 導入時は独立 honesty audit 必須** (orchestrator 責務、CLAUDE.md「Independent honesty audit」)。`llr_split_from_density_factorize_pi` の `@residual(plan:...)` 分類正しさ + bridge/subadd 引数が regularity のみ (load-bearing predicate なし) を fresh subagent で検証。

## 失敗判定 / 撤退ライン (plan 全体)

- **Phase 1 で >200 行 → `h_llr_split` 改良不能** → `=ᵐ[μ]` を density 表現に swap した形で **honest hyp 維持** (現状から進歩なし扱い)、Phase 2 は **断念**。本 plan は Phase 0 + Phase 3 (AWGN staged 確認) のみで close、suspect tag は slug 更新だけ (`(differential-entropy-plan)` → `(multivariate-diffentropy-subadditivity-plan)`)。
- **Phase 2 re-open (2026-05-29)**: Phase 2b (density split discharge) が >250 行 or 新 Mathlib 壁に当たる → 段階着地点 A (structural genuine + density split 1 点 sorry) で stop。**現状 (subadd 丸ごと sorry) より strictly honest な前進**なので、honest hyp 温存への後退ではない。n 変数 sorry は `llr_split_from_density_factorize_pi` 1 点に局所化し `@residual(plan:multivariate-diffentropy-subadditivity-plan)` で残置。`@audit:suspect` 形 (honest hyp bundling) への差し戻しは禁止 (tier 4 = sorry-routed より less honest)。
- **(旧、2026-05-25 撤退ライン、誤診と判明)**: ~~Phase 2 案 A / 案 B 双方で行き詰まる (>250 行) → n 変数のみ honest hyp 温存~~。再調査で「自作不能ではなく自作未着手」と判明、撤退ライン未発動 (close 再開)。
- **`sorry` は残さない** (CLAUDE.md 撤退ライン規約)。`:True` placeholder / 結論型≡仮説型 / 退化定義の悪用は禁止。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### 2026-05-24 起草 (Wave 2)

- **本 plan の前提診断**: `MultivariateDiffEntropy.lean` の 4 件 `@audit:suspect(differential-entropy-plan)` (L89/L175/L214/L279) は slug 不整合。`differential-entropy-plan.md` (1-D 差分エントロピー plan、`differentialEntropy_le_gaussian_of_variance_le` 等の 1-D max-entropy は DONE-HONEST-HYPS で publish 済) と n 変数 subadditivity bridge の honest hyp bundle (`h_llr_split` Bayes density split + integrability 7 本) は **無関係**。本 plan の slug を SoT として 4 件 tag の付け替え対象を確定。
- **gap は density factorize 配線、Mathlib 壁ではない**と診断: `prod_withDensity` (Mathlib `WithDensity.lean:712`、verbatim 存在) + `rnDeriv_withDensity` (Mathlib 既存) + `Measure.volume_eq_prod` (rfl) の chain で 2 変数 `h_llr_split` は genuine 化可能。**唯一の Mathlib 壁** = `pi_withDensity` (n 変数 joint density = ∏ marginal density) の不在 (inventory §D-1a)。これは Phase 2 案 A (2 変数 induction で迂回) で回避可能と判断、案 B (`pi_withDensity` 自作 ~80-150 行 + Mathlib PR) を fall-back に。
- **Mathlib-shape 判断**: `jointDifferentialEntropy (μ : Measure (ℝ × ℝ))` および `jointDifferentialEntropyPi (μ : Measure (Fin n → ℝ))` の codomain 選択は **既存実装** (`MultivariateDiffEntropy.lean:52, 58`) と同じく `ℝ × ℝ` / `Fin n → ℝ` を維持 (not `EuclideanSpace`)。理由: `Measure.volume_eq_prod` (rfl) と `volume_pi` (rfl) で `prod_withDensity` / `Measure.pi` API が直接噛む。`EuclideanSpace` を選ぶと `EuclideanSpace.volume` (内積空間 Haar) で乖離 (inventory §D-1)。
- **BM closure plan §Phase 3 との接続**: BM closure plan §Phase 3 (entropy 形 BM 特化) は `IsUniformOnEntropyLogVol` 3 本 honest hyp を採用しており、現状 `jointDifferentialEntropyPi_le_sum` (subadditivity) には依存していない。ただし将来 BM closure の uniform=log-vol 3 hyp を Jensen 積分形 (`Real.concaveOn_negMulLog` + `ConcaveOn.le_map_integral`、両者 Mathlib 在庫 OK) で discharge する別 sub-plan が起こる場合は、本 plan の Phase 2 (n 変数 subadditivity) が **先行 close** 前提となる可能性あり (inventory §C: subadditivity の数学的核 `KL(joint ‖ ∏marginals) ≥ 0` を持つため)。逆方向接続: BM closure plan の判断ログ #4 (Wave 2) で本 plan の起草を明示済。
- **AWGN `IsContinuousAEPGaussian` は本 plan 対象外**: `AWGNAchievabilityDischarge.lean:140` の predicate (`@audit:staged(continuous-aep-gaussian)`) は continuous SMB / n-dim differentialEntropy の Mathlib 壁 (type (b) = 解析の壁) で staged 維持。L32 / L117 の docstring 内 `differential-entropy-plan` 言及は **散文引用** であって `@audit:` tag ではない (Phase 3 で再確認)。本 plan の Phase 3 は plan-side reflection のみ。
- **proof-log: yes** (Phase 1-2): `prod_withDensity` + `rnDeriv_withDensity` の chain で `Real.log_mul` の正性前提 (density > 0 a.e.) が `=ᵐ[μ]` filter とどう絡むかは試行錯誤の余地、`docs/proof-logs/proof-log-multivariate-diffentropy-subadditivity.md` に手数ログを残す。

### 2026-05-25 Wave 3 (commit `0fe2ad4`)

- **Phase 1 着地 (2 変数 genuine 化)**: 計画通り `prod_withDensity₀` + `rnDeriv_withDensity₀` + `rnDeriv_mul_rnDeriv` + `Measure.volume_eq_prod` (rfl) chain で `h_llr_split` を genuine produce、`_v2` 命名で旧版を `@audit:superseded-by(<v2>)` history record として残す方針を選択 (新規 declaration として `_v2` を立て、旧版を撤去ではなく taxonomy で再分類)。`audit-tags.md:24` 語彙との整合を proof-log で確認済。
- **Phase 2 honest withdrawal (Mathlib gap)**: 案 A (2 変数 induction) を ~250 行まで実装した結果、`MeasurableEquiv.piFinSuccAbove` 経由の reshape 各 step で **generic `withDensity_map`** (`(μ.withDensity g).map e = (μ.map e).withDensity (g ∘ e.symm)`) が Mathlib 不在と判明、撤退ライン §"案 A / 案 B 双方で >250 行" 適用。proof-log §"meta — observations" の重要 finding: 案 B (`pi_withDensity` 自作) も同 gap を内包するため fall-back では不解消、本 plan の case-B-as-fallback labeling は **gap の階層を 1 段 misanalyse** していた (真の gap は `pi_withDensity` より 1 階層下の generic `withDensity_map`)。Phase 2 計画文は再開時参照のため保持、本 sub-plan は Phase 1 着地 + Phase 2 withdrawal で close。
- **再開条件の明示**: Mathlib PR `Measure.map_withDensity` merge or 自作 ~80-150 行 helper bridge のいずれかが必要。PR 未提出 (2026-05-25)、将来 task。本 plan を再 open するか、`pi-withdensity-bridge-plan` 等の新 sub-plan として spin off するかは再開時判断。
- **着地後タグ状態**: `MultivariateDiffEntropy.lean` の 4 件 `@audit:` tag は (1) L108 `superseded-by(klDiv_prod_marginals_toReal_eq_sum_sub_joint_v2)`、(2) L198 `superseded-by(jointDifferentialEntropy_le_sum_v2)`、(3) L237 `suspect(multivariate-diffentropy-subadditivity-plan)` (n 変数 KL bridge residual)、(4) L302 `suspect(multivariate-diffentropy-subadditivity-plan)` (n 変数 subadd residual) の 4 種に確定。code SoT 1 箇所で管理 (本 plan に転記しない)。

### 2026-05-29 Phase 2 re-open (前回 withdrawal の誤診修正)

- **gap 誤診の確定**: 前回 Wave 3 の停止理由「generic `withDensity_map` Mathlib 不在 → 案 A 不能」は **gap を誤診**していた。2 つの独立調査 (mathlib-inventory §"2026-05-29 再調査 — n 変数 closure ゲート" + proof-pivot-advisor) で確定。inventory 判定: 不在は事実だが **自作不能ではなく自作未着手** — rnDeriv 特化版 `MeasurableEmbedding.map_withDensity_rnDeriv` (`RadonNikodym.lean:537`、5 行) が脱特化テンプレートを提供、自作部品 + reshape 部品は全て verbatim 在庫。closeable = 自作 helper ~15-25 行 + closure 全体 ~150-250 行 (撤退境界 250 行内)。真の `@residual(wall:...)` 対象は **ゼロ** (現状 `@residual(plan:...)` 分類 honest)。
- **コード現状 drift の発見 (verbatim 確認)**: 計画書旧本文は n 変数 declaration を「honest hyp 温存」と記述していたが、実コード (`Common2026/Draft/Shannon/MultivariateDiffEntropy.lean`、**Draft 配下に移動済**) は既に **sorry-routed** に migrate 済 (`klDiv_pi_marginals_toReal_eq_sum_sub_joint:242` / `jointDifferentialEntropyPi_le_sum:257` ともに regularity hyp underscore + body `sorry` + `@residual(plan:multivariate-diffentropy-subadditivity-plan)`、file docstring §"Phase 2 — withdrawal note" L522-527 で小 cluster sorry-migration 記録)。本 re-open は **sorry-routed → genuine への前進**であって honest hyp への後退ではない。旧本文の行番号 (L90/L176/L215/L280) も全て drift、Phase 2 本文を実行番号 (242/257/113-193/313) で書き直し。
- **構造的洞察 (proof-pivot-advisor、Approach に反映)**: 2 変数 bridge `klDiv_prod_marginals_toReal_eq_sum_sub_joint:113` 本体 (L143-193) は **`prod_withDensity` を使っていない** — `toReal_klDiv_of_measure_eq` (L154) + honest hyp `h_llr_split` (L120-125) + `integral_log_rnDeriv_self_eq_neg` (`:86`、genuine) + `integral_map` の 6 step。`prod_withDensity` は後付け `_v2` (`:285`/`:313`) が `h_llr_split` を discharge する箇所だけ。→ n 変数 bridge の structural 部分 (~60-90 行) は density split 抜きで genuine 化可能、真の壁は density split 1 点に局所化。`klDiv_pi_eq_sum` (`MIChainRule.lean:273`、genuine) は第 1 引数 `Measure.pi` 形要求 → product でない joint μ には直接使えず、per-marginal 引き戻し (`integral_log_rnDeriv_self_eq_neg` + `integral_map`) が正しいルート。
- **2 段着地設計**: Phase 2a (density split を独立補題 `llr_split_from_density_factorize_pi` に切出し、bridge/subadd は structural genuine = 段階着地点 A) / Phase 2b (`withDensity_map_equiv` helper 自作 → `pi_withDensity` → split discharge = 完全 genuine 段階着地点 B)。Phase 2b 行き詰まり時は段階着地点 A で stop (現状より strictly honest な前進)。
- **honesty 設計判断**: density split を `h_llr_split` honest hyp として bridge 引数に戻すのは **禁止** (load-bearing hyp = tier 4/5 = 現 sorry-routed より strictly less honest)。必ず独立補題の sorry body に閉じ込め、bridge/subadd 引数は regularity (`≪` / `Integrable` / instance) のみ。これにより段階着地点 A は honest 撤退口を構造的に確保。
- **再開トリガ不要だった件**: 前回判断ログは「Mathlib PR merge」を再開条件としていたが、PR 不要 (自作 ~15-25 行 helper で道が開く)。`pi-withdensity-bridge-plan` への spin off も不要 (本 plan 1 file 内 helper で足りる、inventory §"Mathlib 壁の列挙" 判定)。
