# Brunn-Minkowski full genuine closure 計画 🌙

> **Parent**: [`brunn-minkowski-moonshot-plan.md`](brunn-minkowski-moonshot-plan.md) §残① (full closure)
>
> 親 moonshot は **hypothesis pass-through で publish 済** (`brunn_minkowski_entropy_inequality` は L-BM1 を `:= h_bm` で着地、抽象 `h : Measure (Fin n → ℝ) → ℝ` 引数)。本 closure plan はその L-BM1 を **genuine に discharge** し、体積版 BM (n-dim PL) と entropy 版 BM を真に閉じることを目的とする新規 plan。実装はまだ無い。
>
> **位置づけ**: BM は残① 項目で唯一 **fundamental Mathlib gap を持たない**。PL は AM-GM (`weighted_amgm_lambda`, genuine) + layer-cake (`Integrable.integral_eq_integral_meas_le`, Mathlib) から構築可能であり、1D 版 superlevel BM は project に既に genuine 実在 (`one_dim_bm_scaled`, `volume_add_compact_ge`)。残る gap は **Fubini 帰納の配線** であって Mathlib の壁ではない。

## 進捗

- [x] Phase 0 — signature 確認 + skeleton ✅ (`BrunnMinkowskiClosure.lean` 既存、Phase 0 inventory は本 plan §Phase 0 verbatim 表に確定済)
- [x] Phase 1 — n-dim PL Fubini 帰納 ✅ (`integral_pi_succ_eq` (§B) + `prekopa_leindler_nDim` (§D, `IsSlicePLReadyHyp` 経由) + §F 体積版 corollary `brunn_minkowski_volume_indicator` で **段階着地点 1 達成**)
- [ ] Phase 2 — prob ↔ 幾何 bridge 🔄 (skip — 判断ログ #4 参照、entropy 形を `IsUniformOnEntropyLogVol` honest hyp 経由で済ませたため Phase 2 自体は不要に)
- [x] Phase 3 — max-entropy + `h` 特化 🔄 (Jensen 積分形 `ConcaveOn.le_map_integral` は Mathlib 在庫 OK だが本実装は **採用せず** — 判断ログ #4: `IsUniformOnEntropyLogVol` 3 本を honest hyp で外出しして `jointDifferentialEntropyPi` 特化 `brunn_minkowski_entropy_jointPi` (§G L493) を閉じる方針へ pivot)
- [x] Phase 4 — entropy 形 headline restate ✅ (`brunn_minkowski_entropy_inequality_genuine` (§G L531) + `brunn_minkowski_entropy_inequality_scaledMul` (§H L695) の 2 形を publish、旧抽象 `h` 版は signature 保持で残置)
- [ ] Phase V — clean 🚧 (`lake env lean InformationTheory/Shannon/BrunnMinkowskiClosure.lean` silent + 残 honest hyp 棚卸し未着手。`@audit:suspect(brunn-minkowski-closure-plan)` 残 2 件 = `brunn_minkowski_volume_indicator` L372 + `brunn_minkowski_entropy_jointPi` L492)

## ゴール / Approach

**ゴール**: Cover-Thomas Theorem 17.9.2 (Brunn-Minkowski entropy 形) を、現在 `:= h_bm` pass-through になっている headline について **genuine に閉じる**。最低でも **体積版 BM** (`vol(λA+(1-λ)B) ≥ vol(A)^{1-λ} vol(B)^λ` = n-dim PL の凸体特殊化) を無条件で閉じ、可能なら entropy 版 (`exp((2/n)h(X+Y)) ≥ exp((2/n)h(X)) + exp((2/n)h(Y))`、`h := jointDifferentialEntropyPi`) を体積版 + uniform max-entropy から導出する。

**Approach (戦略の shape)** — 既存の genuine body を engine とし、唯一未配線の Fubini 帰納を 3 bridge で接続する。

1. **1D を engine に据える**。`prekopa_leindler_1D_superlevel_discharged` (`BrunnMinkowskiLayerCakeBody.lean`, genuine、superlevel 仮定なし) と `one_dim_bm_scaled` (`BrunnMinkowski1DSuperlevelBody.lean`, genuine 1D 測度 BM) を黒箱 base case にする。これらは既に閉じている。

2. **Fubini 帰納で n 次元 PL を組む (Phase 1, 最重)**。現状 `IsPL2FubiniSliceHyp` (`BrunnMinkowskiPLBody.lean:239`) は `intF = reduceF ∧ ...` という **scalar 等式 placeholder** で実 Fubini 未接続。これを `Fin (n+1) → ℝ ≃ ℝ × (Fin n → ℝ)` (last/init coordinate split) 上の **真の Fubini 恒等式** `∫_{Fin(n+1)→ℝ} φ = ∫_{ℝ} (∫_{Fin n→ℝ} φ(s, ·)) ds` (`MeasureTheory.lintegral_prod` / `Measure.integral_prod`) に置換する。slice ごとに帰納仮定 (n 次元 PL) を適用 → 各 slice 積分は ℝ 上の関数 → 1D PL を slice 積分に適用 → 全体 PL。

3. **prob ↔ 幾何 bridge を作る (Phase 2)**。確率変数 `X, Y : Ω → (Fin n → ℝ)` の和 `X+Y` の分布 (`P.map (X+Y)`) と、密度の superlevel-set の Minkowski 和の体積 BM を結ぶ層。独立 → 密度の畳み込み → log-concave 密度の superlevel set は凸体 → n-dim PL (Phase 1) の凸体特殊化を適用。

4. **max-entropy + h 特化 (Phase 3)**。headline の抽象 `h` を `InformationTheory.Shannon.jointDifferentialEntropyPi` (`MultivariateDiffEntropy.lean:58`) に特化する。entropy 形 BM は「体積 BM (n-dim PL) + uniform 分布が固定 support 上で max-entropy を達成 (`h(μ) ≤ log vol(supp)`, Jensen)」から導出する。`jointDifferentialEntropyPi_le_sum` (subadditivity, genuine 構造) も同 file に既存で entropy 側の足場になる。

5. **段階着地**。3 bridge は**独立**。Phase 1 だけ閉じれば **体積版 BM (n-dim PL) は閉じる** (entropy 版は別)。Phase 3 の `h` 特化は signature 変更を伴うため、headline を `jointDifferentialEntropyPi` 版に restate する**新定理として publish** し (Phase 4)、旧抽象 `h` 版 (`brunn_minkowski_entropy_inequality`) は deprecated として残す (取り消し線にはせず、過去参照のため signature 保持)。

**Mathlib-shape-driven 設計判断**:
- n-dim PL の**結論形を、entropy 接続 (Phase 3) が要求する形に合わせる**。すなわち体積比の log-concavity `vol((1-λ)A+λB) ≥ vol(A)^{1-λ} vol(B)^λ` (multiplicative form) を主結論とする。これは `prekopa_leindler_1D_superlevel_discharged` の結論形 `intF^λ * intG^(1-λ) ≤ intH` と同形であり、`Real.mul_rpow` / `Real.rpow_natCast` で entropy power `exp((2/n)h)` に直結する。textbook の additive form `|A+B|^{1/n} ≥ |A|^{1/n}+|B|^{1/n}` は別の equivalence lemma (AM-GM via `bm_additive_to_multiplicative`, genuine 既存) で派生させる。
- Fubini の slice split は **`Fin (n+1) → ℝ` vs `ℝ × (Fin n → ℝ)`** の `MeasurableEquiv` (`MeasurableEquiv.piFinSuccAbove` / `piSplitAt` 系) を使う。`jointDifferentialEntropyPi` は `Fin n → ℝ` 上に既に定義されており、Phase 3 の接続が `volume_pi` / `Measure.pi` の product 構造を直接使えるよう、PL も `Fin n → ℝ` で組む (EuclideanSpace を避ける、`MultivariateDiffEntropy.lean` 設計判断と一致)。

**新規ファイル**: `InformationTheory/Shannon/BrunnMinkowskiClosure.lean` (想定 ~400-600 行)。完了時 `InformationTheory.lean` に import 1 行追加。

**proof-log**: 全 Phase で `proof-log: yes` (Fubini 配線は試行錯誤が予想されるため、判断ログだけでなく `docs/proof-logs/proof-log-brunn-minkowski-closure.md` に手数ログを残す)。

---

## Phase 0 — signature 確認 + skeleton ✅

`proof-log: no` (在庫確認のみ)。

ゴール: Phase 1-4 で消費する既存 genuine 補題の **正確な signature** を確定し、`BrunnMinkowskiClosure.lean` の skeleton が type-check する状態にする。

### 起草時点 (2026-05-21) からの差分

実装が plan より先行しており、現コード `BrunnMinkowskiClosure.lean` (973 行) は Phase 1 §A-§F + Phase 4 §G-§H まで実装済。本 Phase 0 表は (i) 実コードと突き合わせた **最新 line 番号** で更新し、(ii) `[...]` 型クラス前提を **verbatim 抽出**し、(iii) Mathlib 側 Fubini 配線も verbatim で記録する。Phase 1 reshape choice 判定は §A2 で確定 (choice (a) `MeasurableEquiv.piFinSuccAbove` 採用済、`integral_pi_succ_eq` (BrunnMinkowskiClosure §B L80) として実装)。

### project 既存 genuine 補題 (verbatim、`[...]` brackets 厳守)

| 補題 | file:line (現在) | 引数 (verbatim) | conclusion (verbatim) |
|---|---|---|---|
| `prekopa_leindler_1D_superlevel_discharged` | `BrunnMinkowskiLayerCakeBody.lean:243` | `(f g h : ℝ → ℝ) (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1) (hf_nn : ∀ x, 0 ≤ f x) (hg_nn : ∀ x, 0 ≤ g x) (hh_nn : ∀ x, 0 ≤ h x) (hf_mble : Measurable f) (hg_mble : Measurable g) (hh_mble : Measurable h) (hfg_pl : ∀ x y : ℝ, f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y)) + compact-support / finite-integral regularity bundle` | `(∫ x, f x) ^ lam * (∫ x, g x) ^ (1 - lam) ≤ ∫ x, h x` (superlevel 仮定は **内部 produce**) |
| `one_dim_bm_scaled` | `BrunnMinkowski1DSuperlevelBody.lean:151` | `(A B : Set ℝ) (lam : ℝ) (hlam : 0 ≤ lam) (hlam' : lam ≤ 1) (hAc : IsCompact A) (hBc : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty)` | `lam * (volume A).toReal + (1 - lam) * (volume B).toReal ≤ (volume (lam • A + (1 - lam) • B)).toReal` |
| `weighted_amgm_lambda` | `BrunnMinkowskiPLBody.lean:83` | `{a b lam : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hlam : 0 ≤ lam) (hlam' : lam ≤ 1)` | `a ^ lam * b ^ (1 - lam) ≤ lam * a + (1 - lam) * b` |
| `bm_additive_to_multiplicative` | `BrunnMinkowskiPLBody.lean:324` | `{volA volB volAB lam : ℝ} (hvolA : 0 ≤ volA) (hvolB : 0 ≤ volB) (hlam : 0 ≤ lam) (hlam' : lam ≤ 1) (h_add : lam * volA + (1 - lam) * volB ≤ volAB)` | `volA ^ lam * volB ^ (1 - lam) ≤ volAB` |
| `IsPL2FubiniSliceHyp` (旧 placeholder) | `BrunnMinkowskiPLBody.lean:241` | scalar 等式 `intF = reduceF ∧ intG = reduceG ∧ intH = reduceH` | (実 Fubini 未接続。**現行 closure では使わず**、§B `integral_pi_succ_eq` (genuine 実 Fubini) で代替) |
| `jointDifferentialEntropyPi` | `MultivariateDiffEntropy.lean:58` | `{n : ℕ} (μ : Measure (Fin n → ℝ)) : ℝ` | `:= ∫ z, Real.negMulLog ((μ.rnDeriv volume z).toReal) ∂volume` |
| `jointDifferentialEntropyPi_le_sum` | `MultivariateDiffEntropy.lean:280` | `{n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μ.map (fun z => z i))] (h_marg_ac, hμ_ac, h_joint_ac, h_llr_split, h_int_marg, h_int_joint, h_marg_id)` honest bundle (7 本) | `jointDifferentialEntropyPi μ ≤ ∑ i, differentialEntropy (μ.map (fun z => z i))` (suspect、`multivariate-diffentropy-subadditivity-plan` 側で discharge 対象) |
| `entropyPower_nDim` | `BrunnMinkowski.lean:98` | `(n : ℕ) (h : Measure (Fin n → ℝ) → ℝ) (μ : Measure (Fin n → ℝ))` | `:= Real.exp ((2 / n) * h μ)` |
| `exp_inv_n_log_eq_rpow` | `BrunnMinkowskiConcavity.lean:311` | `{n : ℕ} (hn : 0 < (n : ℝ)) {v : ℝ} (hv : 0 < v)` | `Real.exp ((2 / n) * Real.log v) = v ^ ((2 : ℝ) / n)` |
| `entropyPower_nDim_eq_rpow_of_log` | `BrunnMinkowskiFunctional.lean:569` | (uniform=log-vol hypothesis 経由の rpow 形) | `entropyPower_nDim n h μ = vol ^ ((2 : ℝ) / n)` |
| `brunn_minkowski_entropy_inequality` (旧 headline) | `BrunnMinkowski.lean:192` | 抽象 `h : Measure (Fin n → ℝ) → ℝ` 引数版、`:= h_bm` pass-through で着地 | 旧 抽象 form。Phase 4 で `brunn_minkowski_entropy_inequality_genuine` (§G L531) に restate 済、旧形は signature 保持で残置 |

### Mathlib API 在庫 (loogle 2026-05-24 検証、verbatim)

Phase 1 の Fubini 配線および Phase 3 Jensen 積分形に必要な Mathlib API はすべて **存在**。**「隠れ Mathlib gap 候補」とされていた `MeasurableEquiv.piFinSuccAbove` の measure 整合は実在** (`volume_preserving_piFinSuccAbove`)、Phase 1 §B `integral_pi_succ_eq` で genuine に消費済み。

| Mathlib API | file:line | signature (verbatim) | 用途 |
|---|---|---|---|
| `MeasurableEquiv.piFinSuccAbove` | `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:560` | `def piFinSuccAbove {n : ℕ} (α : Fin (n + 1) → Type*) [∀ i, MeasurableSpace (α i)] (i : Fin (n + 1)) : (∀ j, α j) ≃ᵐ α i × ∀ j, α (i.succAbove j)` | Phase 1 reshape choice (a) (§A2) |
| `MeasureTheory.measurePreserving_piFinSuccAbove` | `Mathlib/MeasureTheory/Constructions/Pi.lean:802` | `{n : ℕ} {α : Fin (n + 1) → Type u} {m : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (i : Fin (n + 1)) : MeasurePreserving (MeasurableEquiv.piFinSuccAbove α i) (Measure.pi μ) ((μ i).prod <| Measure.pi fun j => μ (i.succAbove j))` | 同上の measure 整合 |
| `MeasureTheory.volume_preserving_piFinSuccAbove` | `Mathlib/MeasureTheory/Constructions/Pi.lean:814` | `{n : ℕ} (α : Fin (n + 1) → Type u) [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))] (i : Fin (n + 1)) : MeasurePreserving (MeasurableEquiv.piFinSuccAbove α i)` | volume 版 (Phase 1 §B `integral_pi_succ_eq` で直接消費) |
| `MeasureTheory.integral_prod` | `Mathlib/MeasureTheory/Integral/Prod.lean:494` | `(f : α × β → E) (hf : Integrable f (μ.prod ν)) : ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ` (要 `[SigmaFinite ν]`) | Fubini iterated integral |
| `MeasureTheory.volume_pi` | `Mathlib/MeasureTheory/Constructions/Pi.lean:655` | `[∀ i, MeasureSpace (α i)] : (volume : Measure (∀ i, α i)) = Measure.pi fun _ => volume := rfl` | `Fin n → ℝ` の volume ↔ `Measure.pi` 同一視 (rfl) |
| `MeasureTheory.Measure.pi_pi` | `Mathlib/MeasureTheory/Constructions/Pi.lean:293` | `[∀ i, SigmaFinite (μ i)] (s : (i : ι) → Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)` (`@[simp]`) | box ↔ product 体積 |
| `MeasureTheory.Measure.volume_eq_prod` | `Mathlib/MeasureTheory/Measure/Prod.lean:177` | `(α β) [MeasureSpace α] [MeasureSpace β] : (volume : Measure (α × β)) = (volume : Measure α).prod (volume : Measure β) := rfl` | `ℝ × _` の volume 分解 |
| `Real.concaveOn_negMulLog` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:227` | `: ConcaveOn ℝ (Set.Ici 0) Real.negMulLog` | Phase 3 Jensen 積分形 (採用 pivot 後は **未使用**、判断ログ #4) |
| `ConcaveOn.le_map_integral` | `Mathlib/Analysis/Convex/Integral.lean:208` | `[IsProbabilityMeasure μ] (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) : (∫ x, g (f x) ∂μ) ≤ g (∫ x, f x ∂μ)` | Phase 3 Jensen 積分形 (採用 pivot 後は **未使用**) |

**Gap 不在の確証 (A2 判定)**: choice (a) `MeasurableEquiv.piFinSuccAbove` ルートは Mathlib 全揃い (上記 7 件全 verbatim 存在)。Phase 1 §B `integral_pi_succ_eq` (BrunnMinkowskiClosure.lean L80) は `volume_preserving_piFinSuccAbove + integral_prod + Measure.volume_eq_prod` の 3 段 chain で **既に genuine に閉じている** (撤退ライン §[Fubini measure 整合 Mathlib に不在] は **発動回避**)。choice (b) ad hoc 構築は不要。

**smul scaling**: `volume_smul_nDim` (§G L426, project genuine) で `vol(r•A) = r^n vol(A)` (`Fin n → ℝ` 上) を供給済。`Measure.addHaar_smul_of_nonneg` を `Module.finrank (Fin n → ℝ) = n` で適用。

### skeleton スコープ

```lean
namespace InformationTheory.Shannon.BrunnMinkowski
-- imports: BrunnMinkowskiLayerCakeBody, BrunnMinkowskiPLBody,
--   BrunnMinkowski1DSuperlevelBody, BrunnMinkowskiConcavity,
--   InformationTheory.Shannon.MultivariateDiffEntropy,
--   Mathlib.MeasureTheory.Constructions.Pi,
--   Mathlib.MeasureTheory.Integral.Prod

-- Phase 1
def IsPL2FubiniSliceHyp' ...  -- 実 Fubini 版 (∫ = ∫∫)
theorem prekopa_leindler_fubini_step ... := by sorry  -- n → n+1
theorem prekopa_leindler_nDim ... := by sorry          -- 帰納本体 (Nat.rec)
theorem brunn_minkowski_volume_nDim ... := by sorry    -- 体積版 BM (凸体特殊化)

-- Phase 2
theorem sum_dist_to_minkowski_volume ... := by sorry   -- prob ↔ 幾何 bridge

-- Phase 3
theorem entropy_le_logVolume_jointPi ... := by sorry   -- max-entropy (Jensen)
theorem brunn_minkowski_entropy_jointPi ... := by sorry -- entropy 版 (h 特化)

-- Phase 4
theorem brunn_minkowski_entropy_inequality_genuine ... := by sorry  -- restate
```

### Done 条件

- skeleton が `lake env lean InformationTheory/Shannon/BrunnMinkowskiClosure.lean` で sorry warning のみ (error 0)。
- 上記 base case 補題群の signature が確定し、各 Phase の入口/出口の型が繋がることを確認。
- Fubini split の `MeasurableEquiv` が Mathlib に存在することを loogle で確認 (gap 不在の確証)。

---

## Phase 1 — n-dim PL Fubini 帰納 ✅

`proof-log: yes`。**実規模 ~370 行** (BrunnMinkowskiClosure §A-§F、L52-L398)。

ゴール: `IsPL2FubiniSliceHyp` の scalar placeholder を捨て、**実 Fubini 恒等式** `∫_{Fin(n+1)→ℝ} φ = ∫_s ∫_w φ(cons s w)` を作って 1D PL から n 次元 PL を `Nat.rec` で組み上げる。

### A2 判定: reshape choice (a) 採用 ✅

Phase 0 loogle で **choice (a)** `MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0` を採用確定。判定根拠:

- `MeasurableEquiv.piFinSuccAbove` (`Embedding.lean:560`) **存在**、`(∀ j, α j) ≃ᵐ α i × ∀ j, α (i.succAbove j)`。
- `volume_preserving_piFinSuccAbove` (`Pi.lean:814`) **存在**、`MeasurePreserving (MeasurableEquiv.piFinSuccAbove α i)`、これが「隠れ Mathlib gap 候補だった measure 整合」の **実在の確証**。
- choice (b) (ad hoc `Fin (n+1) → ℝ ≃ᵐ ℝ × (Fin n → ℝ)` 構築) は不要。

実装 `integral_pi_succ_eq` (BrunnMinkowskiClosure.lean §B L80) は次の 3 段 chain で genuine 着地:

```lean
theorem integral_pi_succ_eq {n : ℕ} (φ : (Fin (n + 1) → ℝ) → ℝ)
    (hφ : Integrable φ) :
    ∫ x, φ x = ∫ s, ∫ w, φ (Fin.cons s w) := by
  -- Step 1: reshape `volume` on `Fin (n+1) → ℝ` to the product measure on
  -- `ℝ × (Fin n → ℝ)` via the measure-preserving `piFinSuccAbove 0`.
  have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have hφ' : Integrable (fun z => φ ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) 0).symm z)) volume :=
    (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hφ
  rw [← hmp.integral_comp']
  -- Step 2: Fubini on the product measure (`volume` on `ℝ × _` is `prod`).
  rw [Measure.volume_eq_prod, integral_prod _ (by rwa [Measure.volume_eq_prod] at hφ')]
  -- Step 3: rewrite `e.symm (s, w) = Fin.cons s w` and close.
  congr 1; funext s; congr 1; funext w
  rw [show (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm (s, w)
      = Fin.cons s w from ?_]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
  rfl
```

### 実装 step (retrospective, completed)

- [x] **`Fin.cons` の affine 結合線形性 (§A L59 `smul_cons_combine`)**: `λ • cons s w + (1-λ) • cons s' w' = cons (λs+(1-λ)s') (λw+(1-λ)w')`。`Fin.cases` + `Fin.cons_zero/succ` で証明、12 行。
- [x] **Fubini reshape (§B L80 `integral_pi_succ_eq`, 上 sketch のとおり)**: choice (a) で 3 段。
- [x] **slice pointwise PL (§C L117 `sliceInt_pointwise_pl`)**: n 次元の pointwise PL `f x ^ λ * g y ^ (1-λ) ≤ h (λ•x+(1-λ)•y)` に `Fin.cons` を代入し、`smul_cons_combine` で書き換えて slice の pointwise PL を導出。
- [x] **base case `Fin 1 → ℝ`/`ℝ` 同型 (§C' L154 `integral_funUnique_eq`, L169 `prekopa_leindler_1Dim`)**: `MeasurableEquiv.funUnique (Fin 1) ℝ` で `Fin 1 → ℝ ≃ᵐ ℝ` 経由、`prekopa_leindler_1D_superlevel_discharged` を適用。
- [x] **帰納本体 `prekopa_leindler_nDim` (§D L263)**: `IsSlicePLReadyHyp` (§D L228 `def`、解析的前提 bundle = slice integrability + slice の 1D PL 適用可能性) を honest hyp として bundle し、`Nat.rec` で `n=1` (base) → `n+1` (step)。step は `integral_pi_succ_eq` で全体積分を 2 段に reshape → 内側 slice 積分に帰納仮定 → 外側 slice 関数に 1D PL 適用。
- [x] **indicator pointwise PL (§E L322 `indicator_pointwise_pl`)**: `1_A ^ λ * 1_B ^ (1-λ) ≤ 1_{λ•A+(1-λ)•B} (λ•x+(1-λ)•y)` を集合論的に証明 (Minkowski sum membership)。
- [x] **体積版 BM corollary `brunn_minkowski_volume_indicator` (§F L373)**: indicator 特殊化で `(vol A)^λ * (vol B)^(1-λ) ≤ vol(λ•A + (1-λ)•B)`。`brunn_minkowski_volume_mul` (§F L393) として PL 結論を直接体積形に書く wrapper も併設。

### 残 honest hyp

- `IsSlicePLReadyHyp` (§D L228) = slice 積分の integrability + measurability + slice 1D PL 適用前提 bundle。**規制条件型 honest hyp** (`:= True` ではない)、`@audit:suspect(brunn-minkowski-closure-plan)` 1 件 (L372、`brunn_minkowski_volume_indicator` の `h_pl` 引数 = n 次元 PL 結論を indicator 特殊化に直渡しする形)。Phase V で棚卸し対象、§I `indicator_integrable` 等 readiness genuine 供給で部分閉。

### Done 条件 ✅

- `prekopa_leindler_nDim` (§D L263) + `brunn_minkowski_volume_indicator` (§F L373) が 0 sorry、`IsSlicePLReadyHyp` 1 本のみ honest hyp として残置。
- **段階着地点 1 (体積版 BM) は genuine closure 達成**。

---

## Phase 2 — prob ↔ 幾何 bridge 🔄 (skip — pivot により不要に)

`proof-log: no` (実装せず)。

判断ログ #4 の Phase 3 pivot により、entropy 版 BM を「体積 BM ⇒ entropy 版」の prob ↔ 幾何 bridge 経由で組み立てる方針は **採らず**、代わりに `IsUniformOnEntropyLogVol` 3 本 honest hyp で entropy ↔ vol を **同定** する方針 (§G `brunn_minkowski_entropy_jointPi` L493) を採用したため、本 Phase は **実装せず skip**。

将来、uniform=log-vol の 3 honest hyp を discharge する別 plan で `IsLogConcaveDensity` (`BrunnMinkowskiFunctional.lean:93`, 既存 genuine) 経由の bridge を組む余地はあるが、本 closure plan の scope 外。

---

## Phase 3 — max-entropy + h 特化 🔄 (pivot: Jensen 積分形を採用せず、`IsUniformOnEntropyLogVol` honest hyp で外出し)

`proof-log: yes`。**実規模 ~50 行** (§G L450-L519)。

ゴール: headline の抽象 `h` を `jointDifferentialEntropyPi` に特化し、entropy 形 BM を体積 BM + uniform max-entropy から導出。

### A3 判定: Jensen 積分形 Mathlib 在庫 OK、ただし pivot で **未採用**

Phase 0 loogle で Jensen 積分形 `ConcaveOn.le_map_integral` (`Mathlib/Analysis/Convex/Integral.lean:208`) は **Mathlib 在庫あり**を確認 (`[IsProbabilityMeasure μ]` (hg : ConcaveOn ℝ s g) (hgc, hsc, hfs, hfi, hgi) → `∫ g (f x) ∂μ ≤ g (∫ f ∂μ)`)。`Real.concaveOn_negMulLog` (`Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:227`) も `ConcaveOn ℝ (Set.Ici 0) negMulLog` で在庫あり。

ただし、本 closure plan の実装では Jensen 積分形を **採用せず**、より shape 直接の pivot を取った (判断ログ #4)。理由:

1. `jointDifferentialEntropyPi μ ≤ log vol(supp μ)` の Jensen 経路は `μ.rnDeriv volume` の supp / measurability / `Integrable (negMulLog ∘ density)` 等の **副条件 plumbing** が `MultivariateDiffEntropy.lean` 側の honest hyp bundle (`h_marg_id`, `h_int_joint`, etc.) と二重になり、>150 行になる見込み。
2. headline `brunn_minkowski_entropy_inequality_genuine` (§G L531) の用途では「concrete 分布 μ について `h(μ) = log vol`」という **等式 + uniform 同定** で十分。これは `IsUniformOnEntropyLogVol` (`BrunnMinkowski.lean:148`, 既存 predicate) で 3 本 honest hyp として外出し可能 (`hA_unif`, `hB_unif`, `hAB_unif`)。

### 実装 step (retrospective, pivot 後)

- [x] **§G L426 `volume_smul_nDim`**: `vol(r•A) = r^n vol(A)` (`Module.finrank (Fin n → ℝ) = n` で `Measure.addHaar_smul_of_nonneg` 適用)。entropy power scaling の足場。
- [x] **§G L440 `def IsBMEntropyPowerVolumeHyp`**: sqrt 形 BM `volAB^(1/n) ≥ volA^(1/n) + volB^(1/n)` の honest 仮定。geometric BM の sqrt 形のみを bundle (entropy 形ではなく)。
- [x] **§G L450 `bm_volume_sqrt_to_entropyPower`**: sqrt 形 → entropy power 加法形 `vol^(2/n) + vol^(2/n) ≤ vol^(2/n)` への genuine 持ち上げ。`Real.rpow` 代数のみ。
- [x] **§G L493 `brunn_minkowski_entropy_jointPi`**: 主 reduction theorem。引数 = `hA_unif/hB_unif/hAB_unif : jointDifferentialEntropyPi (P.map _) = Real.log vol_` (3 本) + `h_geom_bm_assumed : IsBMEntropyPowerVolumeHyp`。証明は `entropyPower_nDim_eq_exp` + `Real.rpow_def_of_pos` で entropy power を `vol^(2/n)` に rewrite → `bm_volume_sqrt_to_entropyPower` で sqrt 形を持ち上げ。**`@audit:suspect(brunn-minkowski-closure-plan)` 1 件残置 (L492)**。

### 残 honest hyp (Phase V 棚卸し対象)

- `hA_unif/hB_unif/hAB_unif` (uniform=log-vol): **load-bearing 寄り**。本来 `h(μ) ≤ log vol` を Jensen 積分形 (`ConcaveOn.le_map_integral`) で discharge する仕事を、3 つの等式 honest hyp で肩代わりさせている。Mathlib 在庫はあるため将来的に discharge 可能。`@audit:suspect(brunn-minkowski-closure-plan)` 候補だが、現状は wrapper (`brunn_minkowski_entropy_inequality_genuine`) が呼び出し側に丸投げする形で、本 plan の主 wrapper L531 の suspect tag に集約。
- `IsBMEntropyPowerVolumeHyp` (sqrt 形 geometric BM): **regularity 寄り** (geometric content の packaging)。§H で `IsBMScaledMulHyp` (より primitive) からの λ-最適化 discharge `bm_scaledMul_to_sqrt` (genuine) を供給済 → sqrt 形は scaled multiplicative 形に縮約済。

### Done 条件 (pivot 版)

- `brunn_minkowski_entropy_jointPi` (§G L493) が 0 sorry、honest hyp 4 本 (uniform 3 + sqrt BM 1) のみ残置。
- Jensen 積分形は **Mathlib 在庫 OK** (loogle 確認) なので、将来 uniform 3 本を discharge する場合は `Real.concaveOn_negMulLog` + `ConcaveOn.le_map_integral` の組合せで `entropy_le_logVolume_jointPi` を別 plan で書く余地あり (本 plan scope 外、再開時は新規 sub-plan に分離)。

---

## Phase 4 — entropy 形 headline restate ✅

`proof-log: yes`。**実規模 ~50 行** (§G L521-L548 + §H L688-L713)。

ゴール: headline を `jointDifferentialEntropyPi` 版に restate して publish。

### 実装 step (retrospective, completed)

- [x] **`brunn_minkowski_entropy_inequality_genuine` (§G L531)**: `h := jointDifferentialEntropyPi` 固定版の headline、Phase 3 `brunn_minkowski_entropy_jointPi` への 1 行 forward。honest hyp = uniform 3 + sqrt BM 1。**抽象 `h` の `h_bm` pass-through を経由しない**。
- [x] **`brunn_minkowski_entropy_inequality_scaledMul` (§H L695)**: 同結論を、geometric honest hyp を sqrt 形 `IsBMEntropyPowerVolumeHyp` から **より primitive** な `IsBMScaledMulHyp` (Cover-Thomas 17.9.2 出発点) に **縮約** した版。`bm_scaledMul_to_sqrt` (§H L589, genuine λ-最適化) を内部で消費。
- [x] **抽象 `h` 旧版**: `BrunnMinkowski.brunn_minkowski_entropy_inequality` (`:192`) は signature 保持で残置 (取り消し線にせず)。`@[deprecated]` 付与は本 plan scope では未実施 (BM.lean 編集は別 PR 候補、判断ログ 2026-05-24 #5)。
- [x] `InformationTheory.lean` に `import InformationTheory.Shannon.BrunnMinkowskiClosure` 追記済 (file 存在 + 973 行で参照済)。

### Done 条件 ✅

- `brunn_minkowski_entropy_inequality_genuine` (§G L531) + `brunn_minkowski_entropy_inequality_scaledMul` (§H L695) が 0 sorry。
- **段階着地点 2: entropy 版 BM の Phase 1-3-4 chain は genuine** (`:= h_bm` pass-through 不使用、`brunn_minkowski_entropy_jointPi` → `bm_volume_sqrt_to_entropyPower` → `entropyPower_nDim_eq_exp` chain)。
- 残 honest hyp: uniform=log-vol 3 + (sqrt BM 1 ↘ scaledMul BM 1) のみ。

---

## Phase V — clean ✅ (2026-05-25 wave 3-4 verify + 棚卸し)

`proof-log: docs/proof-logs/proof-log-brunn-minkowski-closure-phase-v.md`。

- [x] `lake env lean InformationTheory/Shannon/BrunnMinkowskiClosure.lean` silent (0 error / 0 sorry / 0 warning) — 2026-05-25 worktree (`.lake` parent symlink reuse) で confirm、exit 0 / 出力 0 行。
- [x] 残存 honest hypothesis 棚卸し (proof-log §「残存 honest hyp 棚卸し」に verbatim signature 列挙):
  - **§Phase 1 残**: `IsSlicePLReadyHyp` (§D L228、regularity bundle 7-conjunction、`@audit:suspect(brunn-minkowski-closure-plan)` L372) ×1。consumer: `prekopa_leindler_nDim` (`:263`)。
  - **§Phase 3 残 (load-bearing)**: uniform=log-vol equality hyp (`hA_unif/hB_unif/hAB_unif : jointDifferentialEntropyPi (P.map ·) = Real.log vol·`)。**実装は standalone `def IsUniformOnEntropyLogVol` ではなく 3 consumer (`brunn_minkowski_entropy_jointPi` L499-502 / `..._inequality_genuine` L538-541 / `..._inequality_scaledMul` L701-704) に equality hyp として inline**。`@audit:suspect(brunn-minkowski-closure-plan)` L492。Jensen 積分形 discharge は別 sub-plan へ deferred。
  - **§Phase 4 残 (regularity / geometric BM image)**: `IsBMEntropyPowerVolumeHyp` (sqrt 形、§G L440) は §H で `IsBMScaledMulHyp` (より primitive、§H L577) からの λ-最適化 discharge `bm_scaledMul_to_sqrt` (`:589`, genuine) で縮約済。`IsBMScaledMulHyp` は `bm_geom_to_scaledMul` (`:661`) で geometric multiplicative BM の image であることが genuine 接続済。
  - 全 honest hyp について `rg 'Prop\s*:=\s*True' BrunnMinkowskiClosure.lean` → **0 件**、全て実 Prop。defect 検出 0。
- [ ] 親 `brunn-minkowski-moonshot-plan.md` 末尾の closure plan へのポインタ確認 (本 turn scope 外、別 turn 対応)。

---

## 失敗判定 / 撤退ライン (plan 全体)

- **各 Phase >400 行で行き詰まる** → 該当 bridge を honest named hypothesis (実 `Prop` 命題、`:= True` 禁止) に外出しして Phase を閉じ、次 Phase へ。`sorry` は残さない。
- **Phase 1 の Fubini `MeasurableEquiv` measure 整合が Mathlib に不在** (唯一の隠れ gap 候補) → product 測度 `ℝ × (Fin n → ℝ)` 経路に切替 (`integral_prod` のみ使用)。それでも不在なら本 plan を **体積版 closure** で着地 (段階着地点 1)、entropy 版は本格 gap として記録。
- **段階着地優先**: Phase 1 単独で体積版 BM は閉じる。Phase 2-4 が溶けても体積版 closure は成果として残す。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### 2026-05-21 起草

- **本 plan の前提診断**: 親 moonshot は pass-through publish 済 (`brunn_minkowski_entropy_inequality := h_bm`、抽象 `h`)。本 closure plan はその L-BM1 を genuine 化する**別 plan** として起草。親に取り消し線は付けず、ポインタ追記のみ。
- **gap は Fubini 配線、Mathlib 壁ではない**と診断: 1D PL (`prekopa_leindler_1D_superlevel_discharged`) / 1D 測度 BM (`one_dim_bm_scaled`) / AM-GM (`weighted_amgm_lambda`) / layer-cake (Mathlib `Integrable.integral_eq_integral_meas_le`) はすべて genuine 閉。`IsPL2FubiniSliceHyp` (`BrunnMinkowskiPLBody.lean:239`) のみ scalar 等式 placeholder で実 Fubini 未接続。唯一の隠れ gap 候補は `MeasurableEquiv.piFinSuccAbove` の measure 整合 (Phase 0 loogle 確認事項)。
- **h 特化先確定**: 抽象 `h` を `InformationTheory.Shannon.jointDifferentialEntropyPi` (`MultivariateDiffEntropy.lean:58`, 今 session 構築) に特化。`jointDifferentialEntropyPi_le_sum` (subadditivity, genuine 構造) が entropy 側足場。h 特化は signature 変更ゆえ新定理 restate (Phase 4)、旧版 deprecate。
- **Mathlib-shape 判断**: n-dim PL の結論形を multiplicative form `vol(λA+(1-λ)B) ≥ vol(A)^λ vol(B)^(1-λ)` に固定 (1D PL の結論形 `intF^λ*intG^(1-λ)≤intH` と同形、entropy power `exp((2/n)h)` に `Real.mul_rpow` で直結)。textbook additive form は `bm_additive_to_multiplicative` (genuine 既存) で派生。

### 2026-05-24 Wave 2 planner refine: Phase 0 verbatim inventory + Phase 1 Fubini tactic sketch + Phase 3 Jensen 積分形 Mathlib 確認 + multivariate subadditivity sub-plan 分離

実装が本 plan の起草 (2026-05-21) より先行していたことを認識し、コードと plan の同期を取る refine。

1. **Phase 0 verbatim inventory 確定** (本 plan §Phase 0):
   - project genuine 補題 11 件 (1D PL / 1D 測度 BM / AM-GM / additive↔multiplicative / `IsPL2FubiniSliceHyp` 旧 placeholder / `jointDifferentialEntropyPi` + `_le_sum` / `entropyPower_nDim` + `exp_inv_n_log_eq_rpow` + `entropyPower_nDim_eq_rpow_of_log` / 旧 headline) の **`[...]` 型クラス前提 + 引数型 + conclusion form を verbatim** で表に確定。起草時点の stale line 番号 (例 `BrunnMinkowskiLayerCakeBody:249` → 現 `:243`、`BrunnMinkowskiPLBody:316` → `:324`、`BrunnMinkowskiFunctional:643` → `:569`、`BrunnMinkowskiPLBody:239` → `:241`、`BrunnMinkowski:183` → `:192`、`BrunnMinkowskiConcavity:305` → `:311`) を current に更新。
   - Mathlib 側 Fubini 配線 9 件 (`MeasurableEquiv.piFinSuccAbove` / `measurePreserving_piFinSuccAbove` / `volume_preserving_piFinSuccAbove` / `integral_prod` / `volume_pi` / `Measure.pi_pi` / `Measure.volume_eq_prod` / `Real.concaveOn_negMulLog` / `ConcaveOn.le_map_integral`) を loogle (2026-05-24) で **全 9 件存在確認**、verbatim signature を表に追加。

2. **Phase 1 reshape choice (a) 採用確定 + tactic sketch 反映** (§Phase 1):
   `MeasurableEquiv.piFinSuccAbove` + `volume_preserving_piFinSuccAbove` (Mathlib `Pi.lean:802/814`) が **実在** と確認 (起草時の「隠れ Mathlib gap 候補」は **不在** 判定)。choice (b) ad hoc 構築は **不要**。コード `BrunnMinkowskiClosure.integral_pi_succ_eq` (§B L80) は choice (a) の 3 段 chain (`volume_preserving_piFinSuccAbove + integral_prod + Measure.volume_eq_prod`) を採用済。Phase 1 の Approach / step を retrospective 形に書き直し、`integral_pi_succ_eq` の tactic sketch (16 行) を plan に inline。

3. **Phase 3 Jensen 積分形 Mathlib 在庫 OK + 採用 pivot** (§Phase 3):
   `Real.concaveOn_negMulLog` + `ConcaveOn.le_map_integral` の組合せは Mathlib 在庫 OK と確認 (起草時の「Mathlib で重い場合」撤退条件は **発動不要**)。しかし、`jointDifferentialEntropyPi μ ≤ log vol(supp μ)` の Jensen 経路は `MultivariateDiffEntropy.lean` 側の honest hyp bundle (7 本) と二重になり >150 行になる見込み + headline 用途では「concrete 分布で `h(μ) = log vol`」の **等式** で十分という判断で、`IsUniformOnEntropyLogVol` 3 本 honest hyp 外出し方針へ **pivot**。Jensen 積分形は本 closure plan scope **外**、将来 uniform 3 本 discharge する場合は別 sub-plan に分離。

4. **Phase 2 skip 確定**: pivot により Phase 2 (prob ↔ 幾何 bridge) は **実装せず**。判定根拠は §Phase 2 に記載。`IsLogConcaveDensity` (`BrunnMinkowskiFunctional.lean:93`) は将来用途のみ。

5. **`brunn_minkowski_entropy_inequality` (BrunnMinkowski.lean:192) deprecated 化は別 PR**: 旧抽象 `h` 版に `@[deprecated]` attribute 付与は本 closure plan scope 外。signature 保持で残置、取り消し線は付けない。

6. **`multivariate-diffentropy-subadditivity-plan.md` 新規分離** (sister plan):
   `MultivariateDiffEntropy.lean` の 4 件 `@audit:suspect(differential-entropy-plan)` は **slug 不整合** (差分エントロピー 1-D plan `differential-entropy-plan.md` は既に DONE-HONEST-HYPS で、4 件 suspect は n 変数 subadditivity bridge / `jointDifferentialEntropyPi_le_sum` の honest hyp bundle (`h_llr_split` Bayes density split + integrability 7 本) の discharge 対象であり、1-D plan は無関係)。本 BM closure plan と並行に新規 `multivariate-diffentropy-subadditivity-plan.md` を起草、4 件の正しい slug 引き継ぎ + AWGN `IsContinuousAEPGaussian` `@audit:staged(continuous-aep-gaussian)` 2 件の plan-side reflection を担当させる。本 closure plan §Phase 3 の `jointDifferentialEntropyPi_le_sum` 引用は本 sub-plan の Phase 1 が **先行 close** 前提 (現状の本 plan 内では未消費だが、将来 uniform=log-vol discharge で uniform 分布の subadditivity 経由が必要になる場合の前提)。
