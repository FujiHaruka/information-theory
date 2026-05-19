# Chernoff Information + Hoeffding Tradeoff ムーンショット計画 🌙 (T1-B + T1-D)

<!--
雛形メモ (moonshot-plan-template.md より):
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 削除/廃止された Phase は ~~取り消し線~~ で残す（完全削除しない、過去参照のため）
- 判断ログは append-only。Phase 中の方針変更・撤退・当初仮定の修正を記録
-->

> **Status (2026-05-19)**: **Tier 0 (定義 + 基本性質) publish 済** (`Common2026/Shannon/Chernoff.lean`, ~280 行, 0 sorry, library root 編入完了)。`docs/textbook-roadmap.md` §T1-B (Chernoff) + §T1-D (Hoeffding) を **一括** で扱う 1〜2 セッション (~3-5h) ムーンショット。Stein/Sanov/Csiszar plumbing (`Stein.lean` / `StrongStein.lean` / `SanovLDPEquality.lean` / `CsiszarProjection.lean`) からの **70-80% 再利用** を前提に、新規ファイル `Common2026/Shannon/Chernoff.lean` (T1-B + T1-D 一括、~600-900 行) に publish。
> **Predecessor**: [`chernoff-hoeffding-mathlib-inventory.md`](chernoff-hoeffding-mathlib-inventory.md) (既存率 100%, 自作 4-5 種, ~615-715 行見積)。
> **Goal**: `chernoffInfo P₁ P₂` (Cover-Thomas 11.9.1) と `hoeffdingE2 P₁ P₂ α` (Cover-Thomas 11.7.3-style) を定義し、Bayesian error の指数収束 (T1-B) と Type I/II tradeoff exponent の n-IID 達成性 (T1-D) を `Tendsto` 形 (または `DotEq`) で publish。
> **撤退ライン**: [L-S1] T1-D を別 plan に分離 / [L-S2] Chernoff achievability のみ / [L-S3] 単発形のみ (詳細 §撤退ライン)。

## 進捗

- [x] Phase 0 — Mathlib + Common2026 API 在庫 ✅ → [`chernoff-hoeffding-mathlib-inventory.md`](chernoff-hoeffding-mathlib-inventory.md)
- [x] **Tier 0 publish — Chernoff/Hoeffding 定義 + 基本性質 (`chernoffInfo`, `chernoffInfo_attained`, `chernoffInfo_nonneg`, `hoeffdingE2`, `hoeffdingE2_attained`, `hoeffdingE2_nonneg`, `klDivPmf_self_eq_zero`) ✅** (2026-05-19, 0 sorry, library root 編入済, `Common2026/Shannon/Chernoff.lean` ~280 行)
- [x] **Phase A 残 — `convexOn_chernoffLogZ` (Hölder 凸性) + `chernoffMediator` pmf bridge ✅** (2026-05-19, 0 sorry, +307 行, `Common2026/Shannon/Chernoff.lean` ~663 行)
- [x] **Phase C — Chernoff achievability (rate-side lower bound, `liminf ≥ chernoffInfo`) ✅** (2026-05-19, 0 sorry, +403 行, `Common2026/Shannon/Chernoff.lean` ~1066 行)。`bayesErrorMinPmf` 自前 pmf 形定義 + per-point Hölder min-bound + n-IID sum reshape ⇒ `Filter.le_liminf_of_le` で結論。
- [ ] ~~Phase B — Chernoff lower bound (Sanov LDP per-tilt 経由)~~ → **撤退ライン L-S2 発動で defer** (converse side / rate-side upper bound; 別 plan へ; 判断ログ #8 参照)
- [x] **Phase D 残 — `hoeffdingE2_unique` 一意性 (Csiszar + strict-convex 経由) ✅** (2026-05-19, 0 sorry, 連続性は別件で deferred)
- [x] **Phase E (部分) — `chernoff_lemma_achievability` publish ✅** (`chernoffInfo` を rate の下界として publish; converse は L-S2 で defer)
- [ ] ~~Phase E (full) — `hoeffding_tradeoff` `Tendsto` 形~~ → **撤退ライン L-S1 発動で defer** (Sanov LDP per-Qstar machinery が converse side と共有のため; 判断ログ #8 参照)

## ゴール / Approach

### 最終到達点

新規ファイル `Common2026/Shannon/Chernoff.lean` で 2 主定理 publish:

```lean
/-- Chernoff information `C(P₁, P₂) := -min_{λ ∈ [0,1]} log ∑_x P₁(x)^{1-λ} · P₂(x)^λ`. -/
noncomputable def chernoffInfo (P₁ P₂ : Measure α) : ℝ := ...

/-- Cover-Thomas Theorem 11.9.1: Bayesian error decays at rate `chernoffInfo`. -/
theorem chernoff_lemma
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P₁ P₂ : Measure α) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (hP₁_pos : ∀ x, 0 < P₁.real {x}) (hP₂_pos : ∀ x, 0 < P₂.real {x})
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P₁)
    (hMapJoint : ∀ n, μ.map (jointRV Xs n) = Measure.pi (fun _ : Fin n => P₁)) :
    Tendsto (fun n : ℕ => -((1:ℝ)/n) * Real.log (bayesErrorMin P₁ P₂ n))
      atTop (𝓝 (chernoffInfo P₁ P₂))

/-- Hoeffding tradeoff exponent `E₂(α) := min_{Q : D(Q‖P₁) ≤ α} D(Q‖P₂)`. -/
noncomputable def hoeffdingE2 (P₁ P₂ : α → ℝ) (alpha : ℝ) : ℝ := ...

/-- Hoeffding tradeoff lemma: optimal Type II exponent at Type I level `α`. -/
theorem hoeffding_tradeoff
    (P₁ P₂ : α → ℝ) (hP₁ : ∀ a, 0 < P₁ a) (hP₂ : ∀ a, 0 < P₂ a)
    (hP₁_sum : (∑ a, P₁ a) = 1) (hP₂_sum : (∑ a, P₂ a) = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_le : alpha ≤ klDivPmf P₁ P₂) :
    Tendsto (fun n : ℕ => -((1:ℝ)/n) * Real.log (steinTypeII_at_level P₁ P₂ n alpha))
      atTop (𝓝 (hoeffdingE2 P₁ P₂ alpha))
```

(`bayesErrorMin` / `steinTypeII_at_level` は Phase A / D で確定。Statement 形は Phase C-1 / E で `Tendsto` vs `DotEq` を 1 つに決める。)

### Approach (中核 4 ピース)

**Mathlib-shape-driven** で textbook の `min_λ log ∑ P₁^λ P₂^{1-λ}` を直書きせず、**Mathlib `Measure.tilted` + `integral_llr_tilted_left/right` の結論形に合わせて** mediator 形で定義する。

1. **Tilted mediator T_λ = `P₁.tilted (λ • llrPmf P₂ P₁)`**:
   - `T_λ(x) = P₁(x) · exp(λ · (log P₂ - log P₁)) / Z = P₁(x)^{1-λ} · P₂(x)^λ / Z(λ)`
   - **Mathlib `integral_llr_tilted_left`** が `D(T_λ ‖ P₁)` を `λ · ⟨llrPmf⟩ - log Z` 形に **自動展開**。textbook 形 `chernoffZ` への bridge は equiv 補題 1 本で完結。
   - **設計選択の根拠**: `chernoffInfo` proof 内で頻繁に呼ぶ「`f (tilted μ f)` を `∫⁻ ... ∂μ` に reshape する bridge」が **Mathlib に既に揃っている**ので、textbook 形を直書きすると 50-100 行のブリッジ自作が必要になる (CLAUDE.md "Mathlib-shape-driven Definitions" 節)。

2. **Chernoff 凸性 → min 達成性は Hölder + 拡張**:
   - `log Z(λ)` の `λ` 上での凸性 ⟸ Hölder 不等式 `Z(αλ₁ + βλ₂) ≤ Z(λ₁)^α · Z(λ₂)^β` (Mathlib `Real.inner_le_Lp_mul_Lq_of_nonneg`)
   - `chernoffInfo` の達成性: `IsCompact.exists_isMinOn` (`isCompact_Icc` 上の連続関数)
   - **endpoint λ = 0, λ = 1 が `HolderConjugate (1/λ) (1/(1-λ))` に乗らない** → Phase A-2 / A-3 で **`Set.Ioo 0 1` 内部で Hölder を起動 + 端点は `rpow_zero/rpow_one` 個別 case 経路** に確定 (在庫指摘の Hölder endpoint 問題、判断ログ #2 参照)。

3. **Chernoff lower bound は Sanov LDP per-tilt + matching set**:
   - Each `λ` に対し T_λ 近傍の type class neighborhood `E_n^λ ⊆ TypeCountIndex α n` を組み、`SanovLDPEquality.sanov_ldp_equality` を `P := T_λ`, `Q := P_i` で適用 → `(1/n) log P_i^n(⋃_E_n^λ) → -klDivPmf T_λ P_i`
   - matching set 構成 (Bayes error の per-tilt 達成集合) は per-tilt 5-10 ステップ、Sanov 既存 plumbing で **自前で書く部分は ~50 行に圧縮**。

4. **Chernoff upper bound は Stein-style typicality + tilted LRT**:
   - `steinTypicalSet_Q_prob_le` (`Stein.lean:341`) の **template** を T_λ 上に流用:
     `T_λ^n` typicality set 上で `(P_i)^n(T_λ^n) ≤ exp(-n · klDivPmf T_λ P_i)` を取り、Bayes error を上下から挟む。
   - **rare regions 分割** (Cover-Thomas 11.9.1 proof の standard) で 1/2 · min(P₁^n(B^c), P₂^n(B)) の上界化。

5. **Hoeffding `min` 達成性は Csiszar projection の直接適用**:
   - 制約集合 `K := {Q ∈ stdSimplex | klDivPmf Q P₁ ≤ alpha}` の閉性 ⟸ `continuous_klDivPmf_left P₁`
   - 非空 ⟸ `P₁ ∈ K` (即ち `klDivPmf P₁ P₁ = 0 ≤ alpha`)、補助補題 `klDivPmf_self_eq_zero` (~5 行)
   - 達成: `csiszar_projection_exists` で `Qstar ∈ K` 存在、`klDivPmf Qstar P₂ = hoeffdingE2 ...`
   - tradeoff `Tendsto` は T1-B Chernoff の Sanov LDP per-tilt machinery を **再利用**: `Qstar` 周りの type class `E_n^*` で `sanov_ldp_equality` を起動。

### Approach 図

```
Phase 0  : Mathlib + Common2026 API 在庫                       ← 完了済 (in inventory)
           ────────────────────────────────────────────────
Phase A  : chernoffInfo 定義 + 基本性質 + 凸性 + min 達成性    ← 1.0 セッション (1.5-2h)
Phase B  : Chernoff lower bound (Sanov LDP per-tilt)            ← 0.75 セッション (1-1.5h)
Phase C  : Chernoff upper bound (tilted LRT + Stein template)   ← 0.5 セッション (0.75-1h)
           ←──── 撤退ライン L-S2 (Chernoff achievability 単独) ─→
           ────────────────────────────────────────────────
Phase D  : hoeffdingE2 定義 + min 達成性                       ← 0.5 セッション (0.75h)
Phase E  : 主定理 wrapper + Common2026.lean 編入               ← 0.25 セッション (0.5h)
           ←──── 撤退ライン L-S1 (T1-D 分離して別 plan へ) ────→
```

### 規模見積 (再掲)

- 自作 1 (Chernoff defs + 基本性質): ~150-180 行
- 自作 2 (`logZ` 凸性 + min 達成性): ~110 行
- 自作 3 (Sanov-LDP → Chernoff lower bound bridge): ~120-150 行
- 自作 4 (`hoeffdingE2` + tradeoff): ~170 行
- 自作 5 (`klDivPmf_self_eq_zero` 補助): ~5 行
- skeleton / imports / docstring / namespace: ~80-130 行
- **合計**: ~635-745 行 / 中央予測 700 行 (roadmap §T1-B + §T1-D 規模見積 600-900 行 と整合)

### ファイル構成 (Phase E 完了想定)

```
Common2026/Shannon/
  Chernoff.lean              ← 新規 (T1-B + T1-D 一括 publish、~700 行)
  Stein.lean                 ← 既存、変更なし (Chernoff から import)
  StrongStein.lean           ← 既存、変更なし
  SanovLDPEquality.lean      ← 既存、変更なし
  CsiszarProjection.lean     ← 既存、変更なし
  KLDivContinuous.lean       ← 既存、変更なし
  Pinsker.lean               ← 既存、変更なし (本 plan 直接依存なし)
Common2026/InformationTheory/
  Asymptotic.lean            ← 既存、変更なし (`DotEq` notation 利用)
Common2026.lean              ← `import Common2026.Shannon.Chernoff` を追記
```

撤退時 (Phase A-C のみ) は **`Chernoff.lean` 内で Hoeffding 関連を `sorry` 残し** で close、Phase D/E は別 plan (`hoeffding-tradeoff-plan.md`) に切り出し。

## 依存関係

完了済 (再利用可):

- [x] `Common2026/Shannon/Stein.lean` (`llrPmf`, `logLikelihoodRatio`, `steinTypicalSet_*`, `steinOptimalBeta`, `klDiv_pi_eq_n_smul`, `stein_strong_law`, `jointRV`)
- [x] `Common2026/Shannon/StrongStein.lean` (`stein_strong_lemma`, strict `Tendsto` 形)
- [x] `Common2026/Shannon/SanovLDPEquality.lean` (`sanov_ldp_equality`, `roundedTypeIndex`, `klDivIndex`)
- [x] `Common2026/Shannon/CsiszarProjection.lean` (`klDivPmf`, `klDivPmf_strictConvexOn_left`, `csiszar_projection_exists`, `csiszar_projection_unique`, `csiszar_pythagoras_inequality`)
- [x] `Common2026/Shannon/KLDivContinuous.lean` (`klDivSumForm_ofVec`, `klDivSumForm_ofVec_continuous`)
- [x] `Common2026/Shannon/Pinsker.lean` (本 plan 直接依存なし、tilted mediator が必要なら間接)
- [x] `Common2026/InformationTheory/Asymptotic.lean` (`DotEq`, `dotEq_iff_tendsto_log_div`, `exp_decay_N_of_pos`)
- [x] Mathlib `Measure.tilted` family (`tilted`, `tilted_apply`, `isProbabilityMeasure_tilted`, `tilted_tilted`, `integral_tilted`, `integral_exp_tilted`, `rnDeriv_tilted_left/right`)
- [x] Mathlib `LogLikelihoodRatio` family (`llr_tilted_left/right`, `integral_llr_tilted_left/right`, `integrable_llr_tilted_left`)
- [x] Mathlib `KullbackLeibler` family (`klDiv`, `klFun`, `convexOn_klFun`, `klDiv_eq_zero_iff`, `klDiv_compProd_eq_add`, `klDiv_compProd_left`)
- [x] Mathlib `MeanInequalities` (`Real.inner_le_Lp_mul_Lq_of_nonneg`, `Real.geom_mean_le_arith_mean_weighted`)
- [x] Mathlib `Pow.Real` (`rpow_natCast/zero/one/add/mul`, `log_rpow`, `rpow_le_rpow`, `rpow_nonneg/pos`)
- [x] Mathlib `Topology.Order.Compact` (`IsCompact.exists_isMinOn`)
- [x] Mathlib `Analysis.Convex.SpecificFunctions.Basic` (`convexOn_exp`, `strictConcaveOn_log_Ioi`, `convexOn_rpow`)

---

## Phase 0 — Mathlib + Common2026 API 在庫 ✅

完了 (`docs/shannon/chernoff-hoeffding-mathlib-inventory.md`, 652 行)。

主結論:

- **既存 API カバレッジ 100%** (実体ベース 35 項目): Mathlib `Measure.tilted` + `LogLikelihoodRatio` + Common2026 Stein/Sanov/Csiszar plumbing で完備
- **自作 4-5 種**: `chernoffInfo` / `hoeffdingE2` 定義 + `chernoffInfo_attained` + Sanov-LDP→Chernoff bridge + `klDivPmf_self_eq_zero` 補助
- **規模見積**: ~615-715 行 (roadmap 中央予測 700 行と整合)
- **撤退ライン現時点で発動なし**、新規撤退ライン 3 件を本 plan に追加 (§撤退ライン)

---

## Phase A — Chernoff exponent 定義 + 基本性質 📋

### スコープ

`chernoffLogTilt`, `chernoffMediator`, `chernoffZ`, `chernoffInfo` を定義し、基本性質 (連続性、凸性、`Z(0) = Z(1) = 1`, `chernoffInfo ≥ 0`, **`min` 達成性**) を確定。

### Done 条件

- `chernoffInfo P₁ P₂ ≥ 0`、`chernoffInfo P₁ P₂ = -log (chernoffZ P₁ P₂ λ*)` を満たす `λ* ∈ Icc 0 1` の存在 (`chernoffInfo_attained`)
- `klDivPmf_self_eq_zero` 補助補題 (Hoeffding 側で再利用)
- `lake env lean Common2026/Shannon/Chernoff.lean` で Phase A までの skeleton + Phase A 本体が clean (Phase B-E は `sorry`)

### ステップ

- [ ] **A-0 skeleton**: 全主定理 + 補助補題を `:= by sorry` で並べた skeleton を Write、LSP 診断で type-check OK 確認 (CLAUDE.md "Skeleton-driven Development")。

- [ ] **A-1 定義 4 種** (`chernoffLogTilt`, `chernoffMediator`, `chernoffZ`, `chernoffInfo`):
  ```lean
  noncomputable def chernoffLogTilt (P₁ P₂ : Measure α) (lam : ℝ) : α → ℝ :=
    fun x => lam * (llrPmf P₂ P₁ x)

  noncomputable def chernoffMediator (P₁ P₂ : Measure α) (lam : ℝ) : Measure α :=
    P₁.tilted (chernoffLogTilt P₁ P₂ lam)

  noncomputable def chernoffZ (P₁ P₂ : Measure α) (lam : ℝ) : ℝ :=
    ∑ x : α, (P₁.real {x}) ^ (1 - lam) * (P₂.real {x}) ^ lam

  noncomputable def chernoffInfo (P₁ P₂ : Measure α) : ℝ :=
    -(sInf ((Real.log ∘ chernoffZ P₁ P₂) '' Set.Icc (0:ℝ) 1))
  ```

- [ ] **A-2 端点値**: `chernoffZ P₁ P₂ 0 = 1`, `chernoffZ P₁ P₂ 1 = 1` (`rpow_zero` + `rpow_one` + `IsProbabilityMeasure.measure_univ`)。系として `Real.log (chernoffZ P₁ P₂ 0) = 0`、`Real.log (chernoffZ P₁ P₂ 1) = 0`。

- [ ] **A-3 strict positivity**: `0 < chernoffZ P₁ P₂ lam` for `lam ∈ Icc 0 1` (full-support `hP₁_pos`, `hP₂_pos` + `rpow_pos_of_pos` + `Finset.sum_pos`)。`Real.log (chernoffZ ...)` の domain 確認。

- [ ] **A-4 連続性**: `Continuous (fun lam => chernoffZ P₁ P₂ lam)` および `Continuous (fun lam => Real.log (chernoffZ P₁ P₂ lam))` on `Icc 0 1` (`Real.continuous_rpow`, `Real.continuous_log` の合成、A-3 で `> 0` 保証)。

- [ ] **A-5 凸性** (`convexOn_chernoffLogZ`):
  ```lean
  lemma convexOn_chernoffLogZ (P₁ P₂ : Measure α)
      (hP₁ : ∀ x, 0 < P₁.real {x}) (hP₂ : ∀ x, 0 < P₂.real {x}) :
      ConvexOn ℝ (Set.Icc (0:ℝ) 1) (Real.log ∘ chernoffZ P₁ P₂)
  ```
  - **証明 sketch**: Hölder 不等式 `Real.inner_le_Lp_mul_Lq_of_nonneg` で `Z(αλ₁ + βλ₂) ≤ Z(λ₁)^α · Z(λ₂)^β` を取り、両辺 log で `log Z(αλ₁ + βλ₂) ≤ α log Z(λ₁) + β log Z(λ₂)`。
  - `HolderConjugate (1/α) (1/β)` 構築は `α, β ∈ Ioo 0 1` の場合のみ可能。端点 `α = 0` / `α = 1` は trivial inequality (Z 不等式が等号) で個別 case 化。
  - **失敗時 fallback** (撤退ライン #2 trigger): `(1-λ) · D(T_λ ‖ P₁) + λ · D(T_λ ‖ P₂) = -log Z(λ)` 形 (Mathlib `integral_llr_tilted_left/right` から自動展開) を **definition として採用** し、凸性は jointly-convex KL の補題から導く。

- [ ] **A-6 `chernoffInfo_attained`**:
  ```lean
  theorem chernoffInfo_attained (P₁ P₂ : Measure α) (hP₁ : ∀ x, 0 < P₁.real {x}) (hP₂ : ∀ x, 0 < P₂.real {x}) :
      ∃ lam ∈ Set.Icc (0:ℝ) 1, chernoffInfo P₁ P₂ = -(Real.log (chernoffZ P₁ P₂ lam))
  ```
  - A-4 連続性 + `isCompact_Icc` + `IsCompact.exists_isMinOn` で達成、`sInf` を `iInf` 経由で `min` に下ろす。
  - `chernoffInfo P₁ P₂ ≥ 0`: A-2 から `chernoffInfo ≥ -log 1 = 0`。

- [ ] **A-7 `klDivPmf_self_eq_zero`** (補助、Hoeffding 側で再利用):
  ```lean
  lemma klDivPmf_self_eq_zero (P : α → ℝ) (hP : ∀ a, 0 < P a) : klDivPmf P P = 0
  ```
  - unfold + `div_self` + `klFun_one = 0` (Mathlib `KLFun.lean`) で 5 行。

- [ ] **A-8 mediator-tilted bridge** (Phase B/C の入口):
  ```lean
  lemma chernoffMediator_real_singleton (P₁ P₂ : Measure α) (lam : ℝ) (x : α)
      (hP₁ : ∀ x, 0 < P₁.real {x}) (hP₂ : ∀ x, 0 < P₂.real {x}) :
      (chernoffMediator P₁ P₂ lam).real {x} = (P₁.real {x}) ^ (1 - lam) * (P₂.real {x}) ^ lam / chernoffZ P₁ P₂ lam
  ```
  - `tilted_apply'` + `rnDeriv_tilted_left` + `llrPmf` の定義展開で算出。**ENNReal.ofReal 反転に注意** (CsiszarProjection.lean と同様の経路)。

### 工数感

~150-200 行 (定義 + A-2〜A-8 補題 + 凸性 ~80 行)。proof-log `yes`。

### 失敗時 fallback

- **A-5 Hölder 凸性が 100 行を超える**: 撤退ライン #2 発動 → `-log Z(λ) = (1-λ) D(T_λ ‖ P₁) + λ D(T_λ ‖ P₂)` 形に **definition 変更** (`chernoffInfo` を `-sInf ((1-·) * D(T_· ‖ P₁) + · * D(T_· ‖ P₂))` に再定義)。textbook 形は equiv 補題で繋ぐ。

---

## Phase B — Chernoff lower bound (Sanov LDP per-tilt) 📋

### スコープ

Sanov LDP equality (`SanovLDPEquality.sanov_ldp_equality`) を T_λ で per-tilt 起動 → matching set 構成で Bayes error の lower bound `P_e^{(n)} ≥ exp(-n · chernoffInfo) · poly(n)` を取る。

### Done 条件

- `chernoff_lower_bound`: `liminf_n -((1:ℝ)/n) * log (bayesErrorMin P₁ P₂ n) ≤ chernoffInfo P₁ P₂` (= upper bound on the rate ≤ chernoffInfo on the Bayesian-error side)

### ステップ

- [ ] **B-1 `bayesErrorMin` 定義**:
  ```lean
  noncomputable def bayesErrorMin (P₁ P₂ : Measure α) (n : ℕ) : ℝ :=
    sInf { ((Measure.pi (fun _ : Fin n => P₁)) s).toReal / 2 + ((Measure.pi (fun _ : Fin n => P₂)) sᶜ).toReal / 2 | (s : Set (Fin n → α)) (_ : MeasurableSet s) }
  ```
  (符号と prior は 1/2 each で固定。後で general prior 形にしたければ別補題。)

- [ ] **B-2 T_λ neighborhood 型クラス E_n^λ**:
  - `roundedTypeIndex (fun x => (chernoffMediator P₁ P₂ lam).real {x}) n : TypeCountIndex α n` (`SanovLDPEquality.lean:111` 再利用)
  - `E_n^λ := { roundedTypeIndex T_λ n }` (singleton で start、必要なら拡張)

- [ ] **B-3 `sanov_ldp_equality` 起動** (each `λ` で 2 回: P₁ 側 / P₂ 側):
  - `P := chernoffMediator P₁ P₂ lam` (T_λ), `Q := P₁` → `(1/n) log P₁^n(E_n^λ) → -klDivPmf T_λ P₁`
  - `P := chernoffMediator P₁ P₂ lam` (T_λ), `Q := P₂` → `(1/n) log P₂^n(E_n^λ) → -klDivPmf T_λ P₂`
  - `h_minimizer` 仮定: `csiszar_projection_unique` (CsiszarProjection.lean:186) + KL strict convexity (`klDivPmf_strictConvexOn_left`) で each tilt の T_λ minimizer 性を local に整理。
  - **rate identity**: `λ · klDivPmf T_λ P₁ + (1-λ) · klDivPmf T_λ P₂ = -log Z(λ)` (Mathlib `integral_llr_tilted_left/right` の算数組み立て、Phase A-8 bridge 経由)

- [ ] **B-4 matching set 構成**:
  - Bayes-test の rejection region `s_n^λ := { x | T_λ^n(x) is closer to P_₂^n(x) than P_₁^n(x) }`
  - もしくはより直接的に、`s_n := E_n^λ` を rejection set として採用 (singleton type class で十分、後で必要なら expand)
  - `P₁^n(s_n^λ) ≤ exp(-n · klDivPmf T_λ P₁) + o-poly` (Sanov upper、`Sanov.lean:305` `typeClass_Qn_le_klDiv` template)
  - `P₂^n((s_n^λ)^c) ≤ exp(-n · klDivPmf T_λ P₂) + o-poly` (同上、対称)
  - Bayes-error: `(P₁^n s)/2 + (P₂^n s^c)/2 ≤ exp(-n · min(klDivPmf T_λ P₁, klDivPmf T_λ P₂)) + o-poly`
  - λ ranging で `min ≥ chernoffInfo - δ` (Phase A-6 達成性 + B-3 rate identity 経由)。

- [ ] **B-5 liminf 形 wrap-up**:
  - 各 `λ` から `-((1:ℝ)/n) * log bayesErrorMin ... ≤ -log Z(λ) - o(1)`
  - 凸 sInf を取って `liminf_n -((1:ℝ)/n) * log bayesErrorMin ... ≤ chernoffInfo P₁ P₂`

### 工数感

~120-150 行 (per-tilt Sanov 起動 ~50 + matching set 議論 ~70 + asymptotic 結合 ~30)。proof-log `yes`。

### 失敗時 fallback

- **`sanov_ldp_equality` の `h_minimizer` 仮定が per-tilt で組めない (1 セッション以上)**: 撤退ライン #1 発動 → singleton type class `{roundedTypeIndex T_λ n}` を **複数 type を含む neighborhood に拡張** し、`csiszar_pythagoras_inequality` で neighborhood 内の T_λ uniqueness を担保。代替路: T_λ minimizer 性を直接 `klDivPmf_strictConvexOn_left` + `csiszar_projection_unique` で証明し、Sanov LDP の前提に渡す。

---

## Phase C — Chernoff upper bound (tilted LRT + Stein template) 📋

### スコープ

任意の Bayes-decision rule に対し `bayesErrorMin ≥ ?` 形で **lower bound on Bayes error** を取り、`-((1:ℝ)/n) log bayesErrorMin ≥ chernoffInfo - δ` を `limsup` 形で確定する。
Phase B (rate ≤ chernoffInfo) と sandwich → `Tendsto`。

### Done 条件

- `chernoff_upper_bound`: `limsup_n -((1:ℝ)/n) * log (bayesErrorMin P₁ P₂ n) ≥ chernoffInfo P₁ P₂`

### ステップ

- [ ] **C-1 statement 形確定** (judgement #1 で確定): 「`Tendsto` 直書き」 vs 「`DotEq` 形 (`bayesErrorMin ≐ exp(-n · chernoffInfo)`)」 vs 「achievability/converse pair」のいずれを最終形にするかを **Phase A 終了時に決定**。`dotEq_iff_tendsto_log_div` (`Asymptotic.lean:116`) で往復可能、`Tendsto` 形 を main + `DotEq` corollary が現状の Common2026 style と整合。

- [ ] **C-2 tilted LRT**:
  - 任意 rejection set `s ⊆ (Fin n → α)` に対し、`(P₁^n s) + (P₂^n s^c) ≥ ?`。
  - **classic Cover-Thomas trick**: each `x : Fin n → α` で `min(P₁^n(x), P₂^n(x)) ≥ P₁^n(x)^{1-λ} · P₂^n(x)^λ - small` を per-point で取り、sum over `x` で `bayesErrorMin · 2 ≥ ∑_x min(P₁^n(x), P₂^n(x)) ≥ Z(λ)^n` を導出。
  - 具体的には `min(a, b) ≥ a^{1-λ} · b^λ - poly` の per-point 不等式 (Hölder 系または `geom_mean_le_arith_mean_weighted`)。

- [ ] **C-3 multiplicative form**:
  - `bayesErrorMin P₁ P₂ n ≥ (1/2) · Z(λ)^n` for each `λ ∈ Icc 0 1`
  - `-((1:ℝ)/n) log bayesErrorMin ≤ -log Z(λ) + O(log n / n)`
  - sInf over `λ` で `limsup -((1:ℝ)/n) log bayesErrorMin ≤ chernoffInfo P₁ P₂` (逆向き、Phase B と sandwich)。

- [ ] **C-4 `chernoff_lemma` main theorem**:
  - Phase B (`liminf ≤`) + Phase C-3 (`limsup ≤` 逆形) sandwich → `Tendsto`。
  - `tendsto_of_le_liminf_of_limsup_le` 形で結論。

### 工数感

~150-180 行 (per-point min-bound ~60 + sum reshape ~40 + limsup/sandwich ~50)。proof-log `yes`。

### 失敗時 fallback

- **per-point `min ≥ a^{1-λ} b^λ - poly` が組めない (Mathlib に直接補題なし、自前 8-10 行で詰む)**: `Stein.lean:341` `steinTypicalSet_Q_prob_le` の **template** を T_λ に適用 → typicality set 経由で `bayesErrorMin ≥ exp(-n · chernoffInfo)` を取る代替路。**Stein achievability template の流用** で **~70-80% の再利用** が proof-log 主張通り効く想定。

---

## Phase D — Hoeffding `hoeffdingE2` 定義 + min 達成性 📋

### スコープ

`hoeffdingE2` 定義 + `Csiszar projection` の直接適用で達成性。tradeoff の `Tendsto` 形は Phase E。

### Done 条件

- `hoeffdingE2 P₁ P₂ alpha` 定義 + `hoeffdingE2_attained`
- (任意) `hoeffdingE2_continuous_in_alpha` (連続性、Hoeffding tradeoff curve の連続性) — 余裕があれば

### ステップ

- [ ] **D-1 定義**:
  ```lean
  noncomputable def hoeffdingE2 (P₁ P₂ : α → ℝ) (alpha : ℝ) : ℝ :=
    sInf ((fun Q => klDivPmf Q P₂) '' {Q | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha})
  ```

- [ ] **D-2 制約集合の閉性 + 非空**:
  - 閉性: `IsClosed K` where `K := {Q | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha}`
    ⟸ `IsClosed (stdSimplex ℝ α)` (Mathlib 既存) ∩ `IsClosed.preimage continuous_klDivPmf_left (isClosed_Iic alpha)`
  - 非空: `P₁ ∈ K` (A-7 `klDivPmf_self_eq_zero` + `h_alpha_nn`)

- [ ] **D-3 `hoeffdingE2_attained`**:
  ```lean
  theorem hoeffdingE2_attained (P₁ P₂ : α → ℝ) (hP₁ : ∀ a, 0 < P₁ a) (hP₂ : ∀ a, 0 < P₂ a)
      (hP₁_sum : (∑ a, P₁ a) = 1) {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) :
      ∃ Qstar ∈ {Q | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha},
        hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂
  ```
  - D-2 (閉 + 非空) + `csiszar_projection_exists` で達成 (CsiszarProjection.lean:172)
  - **目的関数の reference を `P₂` に取り直し**: `csiszar_projection_exists` の signature は `(P, Q) ↦ klDivPmf P Q` の最小化を `K` 上で取る形。`Q := P₂`、`P` を K 上を動かして minimize の form で **そのまま適用**可能。

- [ ] **D-4 一意性** (任意):
  - `csiszar_projection_unique` + `klDivPmf_strictConvexOn_left` で `Qstar` の一意性 (Hoeffding `Q*_λ` の一意性、tradeoff の Lagrange 経路で活躍)

### 工数感

~60-90 行 (定義 + D-2 ~20 + D-3 ~40 + D-4 ~20)。proof-log `no` (Phase A-7 + Csiszar 直接適用で proof skeleton 明確)。

### 失敗時 fallback

- **`continuous_klDivPmf_left` の引数順衝突** (在庫 §危険 4 参照): 在庫の確認では `(P 変数, Q reference)` 解釈で `klDivPmf Q P₁` (= `Q` 変数, `P₁` reference) と一致するので**そのまま使える**。万一型衝突したら `Function.swap` で対称化版を private lemma で作る (~3 行)。

---

## Phase E — 主定理 wrapper + library 編入 📋

### スコープ

`chernoff_lemma` (T1-B) + `hoeffding_tradeoff` (T1-D) の **最終 statement form を確定** し、`Common2026.lean` に `import Common2026.Shannon.Chernoff` を追記。

### Done 条件

- `chernoff_lemma` `Tendsto` 形 publish (Phase B + C sandwich)
- `hoeffding_tradeoff` `Tendsto` 形 publish (Phase D `min` 達成性 + Sanov LDP per-Qstar の machinery 再利用)
- `Common2026.lean` 更新、`lake env lean Common2026/Shannon/Chernoff.lean` clean
- (任意) `chernoff_lemma_dotEq` corollary (`bayesErrorMin ≐ exp(-n · chernoffInfo)`)

### ステップ

- [ ] **E-1 `chernoff_lemma` 統合**:
  - Phase B (`liminf -((1:ℝ)/n) log bayesErrorMin ≤ chernoffInfo`) + Phase C (`limsup ≤ chernoffInfo`) → `Tendsto`
  - signature 確定 (judgement log #1)

- [ ] **E-2 `hoeffding_tradeoff` 統合**:
  - D-3 `Qstar` を Sanov LDP per-Qstar に渡す ⟹ Phase B 同様 `sanov_ldp_equality` 起動
  - `steinTypeII_at_level P₁ P₂ n alpha` の定義 (`steinOptimalBeta` の variant、Type I level `alpha` を可変化)
  - tradeoff `Tendsto` 形 → `hoeffdingE2`

- [ ] **E-3 `DotEq` corollary** (任意):
  - `dotEq_iff_tendsto_log_div` (`Asymptotic.lean:116`) 経由で `bayesErrorMin ≐ exp(-n · chernoffInfo)` を提示

- [ ] **E-4 library root 編入**:
  - `Common2026.lean` に `import Common2026.Shannon.Chernoff` 追記
  - `lake env lean Common2026.lean` clean 確認

### 工数感

~80-120 行 (E-1 ~30 + E-2 ~60 + E-3 ~10 + E-4 ~5)。proof-log `no` (skeleton 揃ったあとの整地)。

### 失敗時 fallback

- **E-2 `steinTypeII_at_level` 定義が `steinOptimalBeta` の variant として綺麗に出ない**: 撤退ライン L-S1 発動 → T1-D を別 plan `hoeffding-tradeoff-plan.md` に切り出し、本 plan は T1-B (`chernoff_lemma`) のみで publish (Phase D の `hoeffdingE2_attained` は **definition + min 達成性のみ** publish して `Tendsto` 形を defer)。

---

## 撤退ライン

### Scope 縮小ライン (発動時に T1-B/D 完成形を縮小して publish)

- **L-S1**: T1-D を本 plan から分離して T1-B 単独 publish (~600 行)、T1-D は別 plan
  - 発動条件: Phase D / E で `csiszar_projection_exists` の **constraint set 翻訳** が綺麗に書けない、または `steinTypeII_at_level` 定義が想定より複雑化 (1 セッション以上)
  - 縮退後: `chernoff_lemma` + `chernoffInfo_attained` + (任意で) `hoeffdingE2` 定義 + `hoeffdingE2_attained` のみで切り出し、tradeoff `Tendsto` は別 plan へ

- **L-S2**: T1-B achievability (Chernoff lower bound) のみ publish (~300 行)、converse (upper bound, Sanov LDP 経由) は別 plan
  - 発動条件: Phase C で per-point `min ≥ a^{1-λ} b^λ - poly` が組めず、Stein typicality template 流用でも 200 行を超える
  - 縮退後: `chernoff_lemma_achievability : liminf -((1:ℝ)/n) log bayesErrorMin ≤ chernoffInfo` のみ publish

- **L-S3**: 単発形 (`chernoffInfo` の定義 + `chernoffInfo_attained` + `klFun` 周辺の basic 補題) のみ publish (~200 行)、n-IID asymptotic 形は別 plan
  - 発動条件: Phase B Sanov LDP per-tilt 起動の `h_minimizer` 仮定が組めない (在庫指摘の n-IID tilted plumbing 肥大 #1 trigger)
  - 縮退後: `chernoffInfo` / `hoeffdingE2` の **定義 + 凸性 + min 達成性** のみで close、asymptotic 結果は **proof-log で「次セッション」と note**

### 自作 plumbing 肥大ライン (新規)

(在庫 §撤退ライン提案を本 plan に正式 import)

- **L-P1**: **Mathlib `Measure.tilted` を `Measure.pi (fun _ : Fin n => P)` 上で直接持ち上げる plumbing が 200 行を超えた場合**
  - 縮退案: n-IID Chernoff statement を `klDivPmf` 自前形に閉じ込め、Mathlib `tilted` は per-letter まで使い (`P₁.tilted f`)、n-letter `P₁^n` への持ち上げは `klDiv_pi_eq_n_smul` (`Stein.lean:713`) で済ます。

- **L-P2**: **Chernoff `log Z(λ)` の凸性証明が 100 行を超えた場合 (Hölder のうまい持ち込みに失敗)**
  - 縮退案: `(1-λ) D(T_λ ‖ P₁) + λ D(T_λ ‖ P₂) = -log Z(λ)` 形 (Mathlib `integral_llr_tilted_left/right` から自動展開) を **definition として採用**、凸性は KL の jointly convex 補題 (Mathlib にあれば) から導く。Phase A-5 を judgement log で記録して definition 変更。

- **L-P3**: **Hoeffding `tradeoff_lemma` の Type I 側 achievability で `stein_achievability` をそのまま転用しようとして DPI 等の hidden 仮定で詰まる場合 (1 セッション以上)**
  - 縮退案: T1-D を **「`hoeffdingE2` 自身の variational expression のみ」** にスコープ縮退 (L-S1 と組み合わせ)、achievability の n-IID `Tendsto` は T1-B Chernoff 完了後の派生補題に押し出し別 plan へ。

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| **`HolderConjugate` の `1 < p` 両端開** が `λ ∈ Icc 0 1` 端点処理を肥大化させる | **高** (在庫 §危険 3 で特定済) | 中 (Phase A-5 の凸性証明 +30-50 行) | judgement #2 で `Set.Ioo 0 1` 内部 Hölder + 端点別 case 経路に確定。**A-5 の plan 通り**進行で吸収。 |
| Chernoff `min` 達成性が `IsCompact.exists_isMinOn` 一発で出ず、`continuous_log ∘ chernoffZ` の連続性証明が肥大 | 低 | 低 (Phase A-4/A-6 で +10-20 行) | A-3 (`chernoffZ > 0`) を独立補題化、`Real.continuous_log_pos` 経路で連続性を 5 行に押し込む。 |
| Sanov LDP per-tilt `h_minimizer` 仮定が **per-`λ` で個別に組めない** | **中** | 高 (Phase B 全体 ~100 行追加) | `csiszar_projection_unique` + KL strict convexity で **T_λ の neighborhood-uniqueness** を local lemma 化 (~30 行)。最悪 L-P1 / L-S3 発動。 |
| Mathlib `integral_llr_tilted_left/right` の `[IsProbabilityMeasure μ]` 前提を `Measure.pi (fun _ => P₁)` 側で derive する補助が必要 | 中 (在庫 §危険 2 で特定済) | 低 (1-2 行で済む見込み) | Stein.lean で既に通している路線 (`Measure.pi_isProbabilityMeasure` 系の instance) を再利用。 |
| Hoeffding tradeoff `Tendsto` 形の `steinTypeII_at_level` 定義が綺麗に書けない (T1-D 全体の risk) | 中 | 高 (Phase E ~50-80 行追加 or L-S1 発動) | L-S1 発動で T1-D 分離。本 plan は T1-B 単独 + `hoeffdingE2` 定義 + `hoeffdingE2_attained` で publish。 |
| **proof 規模が roadmap 上限 (900 行) を超える** | 中 | 中 (1 セッションで完走できない) | 撤退ライン L-S1〜L-S3 を Phase 単位で発動可能に設計済。Phase C 完了 (Chernoff sandwich) でも publish 価値あり (L-S1 縮退)。 |
| Phase B/C で `bayesErrorMin` の定義が tactic で扱いづらく (sInf-over-set 形)、`sInf` 操作が肥大化 | 低-中 | 中 | `bayesErrorMin` を `iInf` 形 + 達成性補題 (`exists_isMinOn` via `Set` の有限可分性) で書き直し、tactic を `iInf_le` / `le_iInf` 系に統一。 |

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(2026-05-19) statement 形は `Tendsto` 直書きを main、`DotEq` を corollary に**: Common2026 既存 Stein / Sanov / Pinsker の主定理が全て `Tendsto` 直書き形を採用しており (`stein_lemma`, `stein_strong_lemma`, `sanov_ldp_equality`)、Asymptotic.lean の `DotEq` は **wrapper notation** として後付け corollary 化する style が既に確立。本 plan も同 style を採用、`chernoff_lemma` / `hoeffding_tradeoff` は `Tendsto` を main, `DotEq` を corollary。Phase E で `dotEq_iff_tendsto_log_div` (`Asymptotic.lean:116`) を呼ぶだけで往復。

2. **(2026-05-19) Hölder endpoint は `Set.Ioo 0 1` 内部経路 + 端点別 case で確定**: 在庫 §危険 3 で特定された `HolderConjugate` の `1 < p` 両端開問題に対し、**Phase A-5 凸性証明は `Set.Ioo 0 1` 内部で Hölder を起動 + λ = 0 / λ = 1 端点は `rpow_zero` / `rpow_one` で degenerate 化** の 2-case 経路を採用する。endpoint 別経路 (e.g., **A-5 の凸性証明を `Icc → Ioo` の連続拡張で済ます**) は **`convexOn` の `Icc` 上での結論を `Ioo` 上の凸性 + 端点 limit で取り直す** 中間補題が必要になるが、Mathlib `convexOn_of_convexOn_isOpen_extend` 系の有無を Phase A 着手時に loogle で再確認 (現時点では unconfirmed)。

3. **(2026-05-19) Chernoff mediator は `P₁.tilted (λ • llrPmf P₂ P₁)` で確定**: 在庫 §危険 5 で示唆された **対称的 2 つの mediator form** のうち、`P₁.tilted (λ • llrPmf P₂ P₁)` を採用。理由: `integral_llr_tilted_left` (`LogLikelihoodRatio.lean:202`) 経由で `klDiv (T_λ ‖ P₁) = λ · klDiv P₂ P₁ - log Z(λ)` 形が **直接** 出る (Mathlib-shape-driven)。`P₂.tilted ((1-λ) • llrPmf P₁ P₂)` 形は対称的だが、Phase B/C の downstream 補題で `Stein.lean` の `llrPmf P Q` orientation (= `log P - log Q`) と整合させると **左 tilt + P₂/P₁ orientation** の方が convention 一貫。

4. **(2026-05-19) T1-B + T1-D 一括着手で start**: roadmap §T1-D 規模見積 (200-300 行追加) が「T1-B 一括で 600-900 行」と明示しており、Csiszar projection の `csiszar_projection_exists` 直接適用で Hoeffding `min` 達成性が **~60-90 行** に圧縮可能 (在庫 §自作 4 + §自作 5)。Sanov LDP per-tilt の machinery が T1-B / T1-D で **共通** (T1-B は per-`λ`、T1-D は per-`Qstar`) なので、Phase B-E を **共有 plumbing** で進めるほうが分離より工数小。万一 Phase E で T1-D 側が詰まれば撤退ライン L-S1 で分離。

5. **(2026-05-19) Tier 0 で全 publish 形を `α → ℝ` pmf 形に統一**: Plan A-1 では `chernoffMediator = P₁.tilted (lam • llrPmf P₂ P₁)` を Mathlib `Measure` 経路で定義する予定だったが、Tier 0 baseline では **`α → ℝ` pmf 形に統一**して publish した。理由: (i) `chernoffZSum P₁ P₂ lam := ∑ a, (P₁ a)^(1-lam) * (P₂ a)^lam` は textbook 形そのまま、`Real.rpow` 算術だけで完結し、`Measure` ⇄ `α → ℝ` の `Measure.real {x}` bridge を全く要求しない。(ii) `hoeffdingE2` の constraint set `{Q : klDivPmf Q P₁ ≤ α}` が既に `CsiszarProjection.klDivPmf : (α → ℝ) → (α → ℝ) → ℝ` の `α → ℝ` 形で書かれており、両主定義の signature を揃えると Tier 1+ で Lagrange duality / Csiszar Pythagoras 経路が混乱なく合成可能。Mediator `T_λ` を `Measure` 経路で導入するのは Tier 1+ の `chernoff_lemma` (Sanov LDP per-tilt) 着手時に必要になった段階でよい — Tier 0 の publish には不要。これにより Tier 0 で **`logZ` 凸性 (Hölder 経路, plan A-5)** も skip し、`chernoffInfo_attained` を `IsCompact.exists_sInf_image_eq` の 1 発で取った (凸性は Tier 1+ で Sanov LDP per-tilt 起動の `h_minimizer` 仮定整理時に再要請されるが、その時 mediator 形 (`(1-λ)·D(T_λ‖P₁) + λ·D(T_λ‖P₂) = -log Z(λ)`) も同時に必要なので一括でフォロー予定)。

6. **(2026-05-19) Phase A残 (`convexOn_chernoffLogZ` + mediator) と Phase D残 (`hoeffdingE2_unique`) を pmf 形のまま publish**: 判断ログ #5 に従い mediator も pmf 形 (`chernoffMediator P₁ P₂ lam : α → ℝ := (P₁ a)^(1-lam) * (P₂ a)^lam / Z(λ)`) で publish。Mathlib `Measure.tilted` への bridge は Phase B 着手時 (Sanov LDP per-tilt が `Q : Measure α` を要求するため) に必要となるが、Phase A残 + D残のスコープでは不要 — chernoffMediator は pmf として positivity + sum_eq_one + 端点 (lam = 0 → P₁, lam = 1 → P₂) のみ publish すれば Phase B/C で `pmfToMeasure` 経由で Measure に持ち上げ可能。Hölder 凸性は `Real.HolderConjugate.inv_one_sub_inv` (`(1/a, 1/(1-a))` for `0 < a < 1`) + `Real.inner_le_Lp_mul_Lq_of_nonneg` で **95 行**で取れた (撤退ライン L-P2 「100 行超え」を僅かに下回り、L-P2 発動なし)。端点 `a = 0` / `a = 1` は `ConvexOn` 定義の degenerate case (片方の weight が 0、線形結合が片方の端点に退化) で `rfl` 1 発でクリア。`hoeffdingE2_unique` は `klDivPmf_strictConvexOn_left` + midpoint argument + `K` の凸性 (`klDivPmf · P₁` の凸性 from `strictConvexOn.convexOn`) で 50 行。

7. **(2026-05-19) Phase B (Chernoff lower bound) は本 plan の本セッションで未着手、Phase C/E も未着手**: スコープ判定: Phase B-C は `bayesErrorMin` 定義 + Sanov LDP per-tilt + matching set 議論で **2-3 session 必要** (plan 見積 250-330 行 vs 残時間)。本セッションでは Phase A残 + D残のみ完遂 (+307 行) し、合計 663 行 0 sorry で停止。Phase B/C/E は次セッションへ。撤退ライン非発動 (L-S1〜L-S3 / L-P1〜L-P3 いずれも未トリガー)。

8. **(2026-05-19) Phase C achievability を pmf 形 `bayesErrorMinPmf` で publish、Phase B converse + Phase E full は撤退ライン L-S1 + L-S2 発動で defer**: 当初の計画 (plan §Approach) は Phase B/C を **Measure 経路** (`Measure.pi` + Sanov LDP per-tilt + tilted LRT) で進める想定だったが、本セッションでスコープ判定を再度実施した結果:
  - **Phase C は pmf 形で完結可能** ⟸ Cover-Thomas 11.9.1 の per-point Hölder degenerate (`min(a, b) ≤ a^{1-λ} · b^λ`) + n-IID sum reshape (`Finset.sum_pow'` + `Fintype.piFinset_univ`) で `bayesErrorMinPmf ≤ (1/2) Z(λ)^n` を直接導出可能。Measure plumbing 不要。`Filter.le_liminf_of_le` の `IsCoboundedUnder` 部分は `chernoff_rate_le_aux_upper` (~40 行) で uniform upper bound を取得して回避。
  - **Phase B converse は Measure 経路が不可避** ⟸ rate-side upper bound (`limsup ≤ chernoffInfo`) を取るには **Sanov LDP per-tilt** (`sanov_ldp_equality` を `Q := P_i (Measure)`, `P := chernoffMediator P₁ P₂ λ*`) を起動する必要があり、これは `chernoffMediator` を pmf から Measure に lift する `pmfToMeasure` helper + `[IsProbabilityMeasure]` instance の plumbing で **+200-300 行クラス**。1 セッション内では不可能。
  - **撤退ライン L-S2 適用**: Phase B converse を別 plan に分離、本 plan は `chernoff_lemma_achievability` (rate-side lower bound, `liminf ≥ chernoffInfo`) のみで publish。これは Cover-Thomas Theorem 11.9.1 の **半分** (achievability side) で、textbook の意味では「指数収束 rate が少なくとも `chernoffInfo`」を意味する。Mathlib formalization としても**有意義な publish 単位**。
  - **撤退ライン L-S1 連動**: Phase E `hoeffding_tradeoff` (`Tendsto` 形) は Sanov LDP per-Qstar machinery を Phase B converse と共有するため、同様に defer。`hoeffdingE2_attained` (定義 + min 達成性) + `hoeffdingE2_unique` (一意性) は Tier 0 + Phase D 残で既に publish 済 — Hoeffding tradeoff の variational form は使用可能、`Tendsto` 形のみ defer。
  - **次セッション着手予定**: 新規 plan `chernoff-converse-hoeffding-tendsto-plan.md` を立てて Phase B converse + Hoeffding tradeoff `Tendsto` を Sanov LDP per-tilt + per-Qstar machinery で完遂。pmf↔Measure bridge (`pmfToMeasure`) を最初に整地、Phase A残/D残/Phase C achievability 完了の本 plan は **L-S2 状態で close** (Cover-Thomas 11.9.1 achievability side + 11.7.x 定義 + 達成性 + 一意性 を publish)。
  - **本セッションの publish 形**:
    - `chernoff_lemma_achievability : chernoffInfo P₁ P₂ ≤ Filter.liminf (rate n) atTop`
    - `bayesErrorMinPmf` n-IID pmf 形 Bayes error 定義
    - `bayesErrorMinPmf_le_half_Z_pow` (Phase C core inequality)
    - `min_le_rpow_mul_rpow` (per-point Hölder degenerate)
    - 既存 publish: `chernoffInfo` / `hoeffdingE2` 定義 + 達成性 + 非負性 + 一意性 + 凸性 + 対称性 + 端点値 + `chernoffMediator` 性質


9. **(2026-05-19) T1-D Hoeffding tradeoff Tendsto 形 (L-S1 deferred) を別 plan で部分 discharge**: 本 plan §判断ログ #8 で L-S1 適用により defer された Hoeffding tradeoff Tendsto 形について, 新規 plan [`hoeffding-tradeoff-moonshot-plan.md`](hoeffding-tradeoff-moonshot-plan.md) でスコープ縮退付き publish を完了 (本 plan の Phase E は引き続き defer; `Common2026/Shannon/HoeffdingTradeoff.lean` 316 行 0 sorry)。Publish 範囲: `pmfToMeasure` family (pmf↔Measure bridge), `steinTypeII_at_level_pmf` 定義 + 基本性質, `hoeffdingConstraintSet_convex`, `hoeffding_minimizer_ge` (Csiszar Pythagoras 経由), `hoeffding_tradeoff_with_hypothesis` (sandwich Tendsto, achievability/converse を hypothesis として取る形)。**未 discharge**: Phase B 残 (`hoeffdingE2_minimizer_full_support` Qstar full-support は log-singularity gradient argument 必要 ~30-50 行), Phase C achievability (Sanov LDP per-Qstar + acceptance region + Type I 自前 AEP), Phase D converse (Stein typicality template Qstar 流用 + Pythagoras) は次々セッション `hoeffding-tradeoff-sandwich-plan.md` (要新規策定) へ。L-S1 は **partial discharge** 状態に移行 (full Tendsto 形は未完だが scaffolding + variational form publish 済)。
