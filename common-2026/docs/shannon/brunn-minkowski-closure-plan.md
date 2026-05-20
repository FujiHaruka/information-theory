# Brunn-Minkowski full genuine closure 計画 🌙

> **Parent**: [`brunn-minkowski-moonshot-plan.md`](brunn-minkowski-moonshot-plan.md) §残① (full closure)
>
> 親 moonshot は **hypothesis pass-through で publish 済** (`brunn_minkowski_entropy_inequality` は L-BM1 を `:= h_bm` で着地、抽象 `h : Measure (Fin n → ℝ) → ℝ` 引数)。本 closure plan はその L-BM1 を **genuine に discharge** し、体積版 BM (n-dim PL) と entropy 版 BM を真に閉じることを目的とする新規 plan。実装はまだ無い。
>
> **位置づけ**: BM は残① 項目で唯一 **fundamental Mathlib gap を持たない**。PL は AM-GM (`weighted_amgm_lambda`, genuine) + layer-cake (`Integrable.integral_eq_integral_meas_le`, Mathlib) から構築可能であり、1D 版 superlevel BM は project に既に genuine 実在 (`one_dim_bm_scaled`, `volume_add_compact_ge`)。残る gap は **Fubini 帰納の配線** であって Mathlib の壁ではない。

## 進捗

- [ ] Phase 0 — signature 確認 + skeleton (新規 `BrunnMinkowskiClosure.lean` の sorry-driven 出だし) 📋
- [ ] Phase 1 — n-dim PL Fubini 帰納 (最重、`IsPL2FubiniSliceHyp` を実 Fubini に置換) 📋
- [ ] Phase 2 — prob ↔ 幾何 bridge (RV 和の分布 ↔ superlevel-set 体積 BM) 📋
- [ ] Phase 3 — max-entropy + `h` 特化 (`jointDifferentialEntropyPi` に restate、`h(μ) ≤ log vol(supp)`) 📋
- [ ] Phase 4 — entropy 形 headline restate (`jointDifferentialEntropyPi` 版主定理 publish、抽象 `h` 版 deprecate) 📋
- [ ] Phase V — clean (`lake env lean` silent、撤退仮定の棚卸し) 📋

## ゴール / Approach

**ゴール**: Cover-Thomas Theorem 17.9.2 (Brunn-Minkowski entropy 形) を、現在 `:= h_bm` pass-through になっている headline について **genuine に閉じる**。最低でも **体積版 BM** (`vol(λA+(1-λ)B) ≥ vol(A)^{1-λ} vol(B)^λ` = n-dim PL の凸体特殊化) を無条件で閉じ、可能なら entropy 版 (`exp((2/n)h(X+Y)) ≥ exp((2/n)h(X)) + exp((2/n)h(Y))`、`h := jointDifferentialEntropyPi`) を体積版 + uniform max-entropy から導出する。

**Approach (戦略の shape)** — 既存の genuine body を engine とし、唯一未配線の Fubini 帰納を 3 bridge で接続する。

1. **1D を engine に据える**。`prekopa_leindler_1D_superlevel_discharged` (`BrunnMinkowskiLayerCakeBody.lean`, genuine、superlevel 仮定なし) と `one_dim_bm_scaled` (`BrunnMinkowski1DSuperlevelBody.lean`, genuine 1D 測度 BM) を黒箱 base case にする。これらは既に閉じている。

2. **Fubini 帰納で n 次元 PL を組む (Phase 1, 最重)**。現状 `IsPL2FubiniSliceHyp` (`BrunnMinkowskiPLBody.lean:239`) は `intF = reduceF ∧ ...` という **scalar 等式 placeholder** で実 Fubini 未接続。これを `Fin (n+1) → ℝ ≃ ℝ × (Fin n → ℝ)` (last/init coordinate split) 上の **真の Fubini 恒等式** `∫_{Fin(n+1)→ℝ} φ = ∫_{ℝ} (∫_{Fin n→ℝ} φ(s, ·)) ds` (`MeasureTheory.lintegral_prod` / `Measure.integral_prod`) に置換する。slice ごとに帰納仮定 (n 次元 PL) を適用 → 各 slice 積分は ℝ 上の関数 → 1D PL を slice 積分に適用 → 全体 PL。

3. **prob ↔ 幾何 bridge を作る (Phase 2)**。確率変数 `X, Y : Ω → (Fin n → ℝ)` の和 `X+Y` の分布 (`P.map (X+Y)`) と、密度の superlevel-set の Minkowski 和の体積 BM を結ぶ層。独立 → 密度の畳み込み → log-concave 密度の superlevel set は凸体 → n-dim PL (Phase 1) の凸体特殊化を適用。

4. **max-entropy + h 特化 (Phase 3)**。headline の抽象 `h` を `Common2026.Shannon.jointDifferentialEntropyPi` (`MultivariateDiffEntropy.lean:58`) に特化する。entropy 形 BM は「体積 BM (n-dim PL) + uniform 分布が固定 support 上で max-entropy を達成 (`h(μ) ≤ log vol(supp)`, Jensen)」から導出する。`jointDifferentialEntropyPi_le_sum` (subadditivity, genuine 構造) も同 file に既存で entropy 側の足場になる。

5. **段階着地**。3 bridge は**独立**。Phase 1 だけ閉じれば **体積版 BM (n-dim PL) は閉じる** (entropy 版は別)。Phase 3 の `h` 特化は signature 変更を伴うため、headline を `jointDifferentialEntropyPi` 版に restate する**新定理として publish** し (Phase 4)、旧抽象 `h` 版 (`brunn_minkowski_entropy_inequality`) は deprecated として残す (取り消し線にはせず、過去参照のため signature 保持)。

**Mathlib-shape-driven 設計判断**:
- n-dim PL の**結論形を、entropy 接続 (Phase 3) が要求する形に合わせる**。すなわち体積比の log-concavity `vol((1-λ)A+λB) ≥ vol(A)^{1-λ} vol(B)^λ` (multiplicative form) を主結論とする。これは `prekopa_leindler_1D_superlevel_discharged` の結論形 `intF^λ * intG^(1-λ) ≤ intH` と同形であり、`Real.mul_rpow` / `Real.rpow_natCast` で entropy power `exp((2/n)h)` に直結する。textbook の additive form `|A+B|^{1/n} ≥ |A|^{1/n}+|B|^{1/n}` は別の equivalence lemma (AM-GM via `bm_additive_to_multiplicative`, genuine 既存) で派生させる。
- Fubini の slice split は **`Fin (n+1) → ℝ` vs `ℝ × (Fin n → ℝ)`** の `MeasurableEquiv` (`MeasurableEquiv.piFinSuccAbove` / `piSplitAt` 系) を使う。`jointDifferentialEntropyPi` は `Fin n → ℝ` 上に既に定義されており、Phase 3 の接続が `volume_pi` / `Measure.pi` の product 構造を直接使えるよう、PL も `Fin n → ℝ` で組む (EuclideanSpace を避ける、`MultivariateDiffEntropy.lean` 設計判断と一致)。

**新規ファイル**: `Common2026/Shannon/BrunnMinkowskiClosure.lean` (想定 ~400-600 行)。完了時 `Common2026.lean` に import 1 行追加。

**proof-log**: 全 Phase で `proof-log: yes` (Fubini 配線は試行錯誤が予想されるため、判断ログだけでなく `docs/proof-logs/proof-log-brunn-minkowski-closure.md` に手数ログを残す)。

---

## Phase 0 — signature 確認 + skeleton 📋

`proof-log: no` (在庫確認のみ)。

ゴール: Phase 1-4 で消費する既存 genuine 補題の **正確な signature** を確定し、`BrunnMinkowskiClosure.lean` の skeleton (全 helper を `:= by sorry`) が type-check する状態にする。**着手前に必ず Read で確認**する対象は以下 (本 plan 起草時点で確認済の signature を記録、実装時に再確認すること)。

- [ ] **base case 1 (1D PL, genuine)**: `BrunnMinkowskiLayerCakeBody.prekopa_leindler_1D_superlevel_discharged` (`BrunnMinkowskiLayerCakeBody.lean:249`)。`f g hfn : ℝ → ℝ`, `lam`, 非負性 + compact/nonempty/finite regularity + pointwise PL + layer-cake `h_lc` + tail integrable `h_tail` → `intF ^ lam * intG ^ (1 - lam) ≤ intH`。**superlevel 仮定は不要 (内部 produce)**。
- [ ] **base case 2 (1D 測度 BM, genuine)**: `BrunnMinkowski1DSuperlevelBody.one_dim_bm_scaled` (`:151`)。`A B : Set ℝ`, `lam`, `0≤lam≤1`, compact + nonempty → `lam * (vol A).toReal + (1-lam) * (vol B).toReal ≤ (vol (lam•A + (1-lam)•B)).toReal`。`volume_add_compact_ge` (`:90`) がさらに base。
- [ ] **AM-GM (genuine)**: `BrunnMinkowskiPLBody.weighted_amgm_lambda` (`:83`) — `a^lam * b^(1-lam) ≤ lam*a + (1-lam)*b`。additive ↔ multiplicative 橋。
- [ ] **additive → multiplicative (genuine)**: `BrunnMinkowskiPLBody.bm_additive_to_multiplicative` (`:316`) — 体積 additive form から multiplicative form。
- [ ] **置換対象 placeholder**: `BrunnMinkowskiPLBody.IsPL2FubiniSliceHyp` (`:239`) = `intF = reduceF ∧ intG = reduceG ∧ intH = reduceH` (scalar 等式)。`pl2_induction_scalar_combine` (`:264`) / `prekopa_leindler_induction_step` (`:281`) はこの placeholder を rewrite するだけ。**Phase 1 でここを実 Fubini に置換する**。
- [ ] **h 特化先 (genuine 構造)**: `Common2026.Shannon.jointDifferentialEntropyPi` (`MultivariateDiffEntropy.lean:58`) = `∫ z, negMulLog ((μ.rnDeriv volume z).toReal) ∂volume`、および `jointDifferentialEntropyPi_le_sum` (`:272`, subadditivity)。**型クラス前提を verbatim 確認**: `[IsProbabilityMeasure μ]`, `[∀ i, IsProbabilityMeasure (μ.map (· i))]` + 多数の honest hypothesis (`h_marg_ac`, `hμ_ac`, `h_joint_ac`, `h_llr_split`, `h_int_marg`, `h_int_joint`, `h_marg_id`)。
- [ ] **entropy power 換算 (genuine)**: `BrunnMinkowski.entropyPower_nDim` (`BrunnMinkowski.lean:98`) = `Real.exp ((2/n) * h μ)`、`BrunnMinkowskiConcavity.exp_inv_n_log_eq_rpow` (`:305`)、`BrunnMinkowskiFunctional.entropyPower_nDim_eq_rpow_of_log` (`:643`)。
- [ ] **headline 現状**: `BrunnMinkowski.brunn_minkowski_entropy_inequality` (`:183`) = `:= h_bm` pass-through、抽象 `h` 引数。Phase 4 で restate 対象。

### Mathlib API 在庫 (Phase 0 で loogle 確認、本 plan では gap 不在を主張するための候補のみ列挙)

- [ ] **Fubini for `Fin (n+1) → ℝ`**: `MeasureTheory.lintegral_prod` / `MeasureTheory.integral_prod` (∫∫ 恒等式) + `MeasurableEquiv.piFinSuccAbove` または `MeasurableEquiv.piSplitAt` (`Fin (n+1) → ℝ ≃ᵐ ℝ × (Fin n → ℝ)`) + `volume_pi` / `Measure.pi_map_*`。**これが Phase 1 の核心。Mathlib に揃っているはず (gap 不在の主張の根拠) — Phase 0 で signature を verbatim 確認**。
- [ ] **smul on `Fin n → ℝ` の measure scaling**: `Measure.addHaar_smul_of_nonneg` は ℝ で `finrank = 1` で使えた (`one_dim_bm_scaled`)。`Fin n → ℝ` では `Module.finrank (Fin n → ℝ) = n` なので `vol(r•A) = r^n vol(A)`。n-dim scaling が直接 Fubini 帰納に必要かは Phase 1 で判断 (slice ごとに 1D scaling で済む可能性)。

### skeleton スコープ

```lean
namespace InformationTheory.Shannon.BrunnMinkowski
-- imports: BrunnMinkowskiLayerCakeBody, BrunnMinkowskiPLBody,
--   BrunnMinkowski1DSuperlevelBody, BrunnMinkowskiConcavity,
--   Common2026.Shannon.MultivariateDiffEntropy,
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

- skeleton が `lake env lean Common2026/Shannon/BrunnMinkowskiClosure.lean` で sorry warning のみ (error 0)。
- 上記 base case 補題群の signature が確定し、各 Phase の入口/出口の型が繋がることを確認。
- Fubini split の `MeasurableEquiv` が Mathlib に存在することを loogle で確認 (gap 不在の確証)。

---

## Phase 1 — n-dim PL Fubini 帰納 (最重) 📋

`proof-log: yes`。**推定 ~200-400 行**。本 closure の最重リスク。

ゴール: `IsPL2FubiniSliceHyp` の scalar placeholder を **実 Fubini 恒等式**に置換し、1D PL (base case) から n 次元 PL を `Nat.rec` で組み上げる。

### Approach (Phase 内)

`φ : (Fin (n+1) → ℝ) → ℝ` を `ℝ × (Fin n → ℝ)` 上の `ψ (s, w) := φ (Fin.cons s w)` に reshape (`MeasurableEquiv.piFinSuccAbove 0` 等)。Fubini で `∫ φ = ∫_s (∫_w ψ(s, w))`。slice 関数 `sliceIntF s := ∫_w f(s, w)` を定義し:

1. **slice ごとの帰納仮定適用**: 各 `(s, s')` で n 次元 PL (帰納仮定) を `f(s, ·), g(s', ·), h(λs+(1-λ)s', ·)` に適用 → `sliceIntF s ^ λ * sliceIntG s' ^ (1-λ) ≤ sliceIntH (λs + (1-λ)s')`。これが `IsPL2SliceStepHyp` (`BrunnMinkowskiPLBody.lean:248`) の genuine 中身。
2. **slice 積分に 1D PL 適用**: `sliceIntF, sliceIntG, sliceIntH : ℝ → ℝ` に対し 1D PL (`prekopa_leindler_1D_superlevel_discharged`) を適用 → `(∫ sliceIntF) ^ λ * (∫ sliceIntG) ^ (1-λ) ≤ ∫ sliceIntH`。
3. **Fubini で全体に戻す**: `∫ sliceIntF = ∫ f` 等 (Fubini 恒等式) で書き換え → `(∫ f) ^ λ * (∫ g) ^ (1-λ) ≤ ∫ h`。

### step

- [ ] **実 Fubini predicate を定義**: `IsPL2FubiniSliceHyp'` を `intF = ∫ s, sliceIntF s` 形の **実積分恒等式**として定義 (scalar 等式 placeholder を捨てる)。`MeasureTheory.integral_prod` の結論形に合わせる (Mathlib-shape)。
- [ ] **Fubini 恒等式の discharge**: `∫_{Fin(n+1)→ℝ} φ = ∫_s ∫_w φ` を `MeasurableEquiv` reshape + `integral_prod` + `volume_pi` で genuine に証明。**ここが Mathlib API 配線の山場** — `Measure.map` of `MeasurableEquiv` と `volume` の整合 (`volume_pi`, `Measure.pi_pi`)。
- [ ] **slice step の genuine 化**: `IsPL2SliceStepHyp` を帰納仮定から produce (placeholder ではなく実際に n 次元 PL を slice に適用)。slice の pointwise PL 仮定が n 次元の pointwise PL から従うことを `Fin.cons` の linearity (`λ • cons s w + (1-λ) • cons s' w' = cons (λs+(1-λ)s') (λw+(1-λ)w')`) で示す。
- [ ] **帰納本体 `prekopa_leindler_nDim`**: `Nat.rec` で `n=1` (base) → `n+1` (step)。base は `prekopa_leindler_1D_superlevel_discharged` を `Fin 1 → ℝ ≃ ℝ` 経由で適用。
- [ ] **体積版 BM `brunn_minkowski_volume_nDim`**: indicator `f=1_A, g=1_B` で PL を凸体に特殊化 → `vol(λA+(1-λ)B) ≥ vol(A)^λ vol(B)^(1-λ)`。`bm_additive_to_multiplicative` で `|A+B|^{1/n}` additive form も派生。

### 撤退条件

- **>400 行で行き詰まる場合**: slice の integrability / measurability 副条件 (Fubini の前提 `Integrable`) を honest named hypothesis (`IsSliceIntegrableHyp` のような実 `Integrable` 命題、`:= True` ではない) に外出しして抜く。Fubini 恒等式自体 (測度内容) は閉じる方針を維持し、副条件のみ外出し。
- **`MeasurableEquiv.piFinSuccAbove` の measure 整合が Mathlib に無い場合**: これが唯一の隠れ Mathlib gap 候補。Phase 0 loogle で不在が判明したら、slice split を `Fin n → ℝ` 直接ではなく `ℝ × (Fin n → ℝ)` product 測度上で組み (`jointDifferentialEntropyPi` も `Fin n` だが Phase 3 接続で reshape)、product Fubini (`integral_prod`, 確実に存在) だけで閉じる。

### Done 条件

- `prekopa_leindler_nDim` + `brunn_minkowski_volume_nDim` が 0 sorry (または上記 honest 副条件 hypothesis のみ残す)。
- **これが閉じれば体積版 BM は genuine に closure** (段階着地点 1)。

---

## Phase 2 — prob ↔ 幾何 bridge 📋

`proof-log: yes`。**推定 ~100-200 行**。

ゴール: 確率変数 `X, Y` の和の分布 (`P.map (X+Y)`) と superlevel-set 体積 BM (Phase 1) を結ぶ。

### step

- [ ] **独立 → 畳み込み密度**: `IndepFun X Y P` から `P.map (X+Y)` の密度が `X, Y` の密度の畳み込みであること (`MeasureTheory.Measure.map_add` / convolution)。Mathlib の convolution API 在庫を Phase 0 で確認 (`MeasureTheory.Measure.conv` 系の有無)。
- [ ] **log-concave 密度の superlevel set は凸体**: `IsLogConcaveDensity ρ` (`BrunnMinkowskiFunctional.lean:93`, genuine 既存) の superlevel `{x | t ≤ ρ x}` が convex。Phase 1 の凸体 BM を適用可能にする。
- [ ] **bridge 本体 `sum_dist_to_minkowski_volume`**: 上 2 つを合成し、`P.map (X+Y)` の superlevel 体積が `P.map X`, `P.map Y` の superlevel の Minkowski 和体積で下から押さえられる形に。

### 撤退条件

- **convolution API が Mathlib に薄い場合**: 密度の畳み込みを介さず、superlevel set 直接の Minkowski 和包含 (`{ρ_{X+Y} ≥ t} ⊇ {ρ_X ≥ s} + {ρ_Y ≥ t/s}` 型) を honest hypothesis 化。>200 行で発動。
- このbridge は **entropy 版 (Phase 3-4) にのみ必要**。体積版だけで止めるなら Phase 2-3-4 は不要 (段階着地点 1 で完結)。

### Done 条件

- `sum_dist_to_minkowski_volume` が 0 sorry (または honest 仮定)。

---

## Phase 3 — max-entropy + h 特化 📋

`proof-log: yes`。**推定 ~150-250 行**。

ゴール: headline の抽象 `h` を `jointDifferentialEntropyPi` に特化し、entropy 形 BM を体積 BM + uniform max-entropy から導出。

### step

- [ ] **max-entropy `entropy_le_logVolume_jointPi`**: `jointDifferentialEntropyPi μ ≤ log vol(supp μ)` を Jensen (`Real.add_pow_le_pow_mul_pow_of_sq_le_sq` ではなく `Real.inner_le_nnorm` でもなく) — `negMulLog` の凹性 (`Real.strictConcaveOn_negMulLog` / `Real.concaveOn_negMulLog`, Loomis-Whitney `entropy_le_log_image_card` で使った `ConcaveOn.le_map_sum` の連続版 = Jensen 積分形) で。**LW の離散版 (`entropy_le_log_image_card`) が prior**。
- [ ] **uniform が max を達成**: uniform 分布 `μ_unif` で等号 `h(μ_unif) = log vol`。`IsUniformOnEntropyLogVolHypothesis` (`BrunnMinkowski.lean:148`, 既存 predicate) の genuine 中身。
- [ ] **entropy 版 BM `brunn_minkowski_entropy_jointPi`**: 体積 BM (Phase 1-2) の両辺を `exp((2/n)·)` で持ち上げ、max-entropy で `h` を `log vol` に置換 → `exp((2/n)h(X+Y)) ≥ exp((2/n)h(X)) + exp((2/n)h(Y))`。`entropyPower_nDim_eq_rpow_of_log` (genuine 既存) + `BrunnMinkowskiConcavity` の log-exp bridge を使う。

### 撤退条件

- **Jensen 積分形が Mathlib で重い場合**: max-entropy 不等式を honest hypothesis (`h(μ) ≤ log vol`, 実 `≤` 命題) に外出し。>250 行で発動。entropy 版 BM の **体積 BM への還元**自体 (Phase 3 の主目的) は閉じる。

### Done 条件

- `brunn_minkowski_entropy_jointPi` が 0 sorry (または max-entropy のみ honest hypothesis)。

---

## Phase 4 — entropy 形 headline restate 📋

`proof-log: yes`。**推定 ~50-100 行**。

ゴール: headline を `jointDifferentialEntropyPi` 版に restate して publish。

### step

- [ ] **`brunn_minkowski_entropy_inequality_genuine`**: `h := jointDifferentialEntropyPi` 固定版の headline を新定理として publish。本体は Phase 3 の `brunn_minkowski_entropy_jointPi`。
- [ ] **抽象 `h` 版を deprecated 化**: 旧 `brunn_minkowski_entropy_inequality` (`BrunnMinkowski.lean:183`) は signature 保持のまま `@[deprecated]` attribute を付ける案を判断ログに記録 (BM.lean の編集は本 plan scope か別 PR か、Phase 4 で決定)。**取り消し線にはしない** (過去参照のため)。
- [ ] `Common2026.lean` に `import Common2026.Shannon.BrunnMinkowskiClosure` 追記。

### Done 条件

- `brunn_minkowski_entropy_inequality_genuine` が genuine (Phase 1-3 の chain で、抽象 `h` の `h_bm` pass-through を経由しない)。
- **段階着地点 2: entropy 版 BM が genuine closure**。

---

## Phase V — clean 📋

`proof-log: no`。

- [ ] `lake env lean Common2026/Shannon/BrunnMinkowskiClosure.lean` silent (0 error / 0 sorry / 最小 warning)。
- [ ] 残存 honest hypothesis (撤退で外出ししたもの) を棚卸しし、各々が `:= True` ではなく実内容を持つことを確認、proof-log に列挙。
- [ ] 親 `brunn-minkowski-moonshot-plan.md` 末尾に closure plan へのポインタ追記 (本 plan 起草と同時に実施)。

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
- **h 特化先確定**: 抽象 `h` を `Common2026.Shannon.jointDifferentialEntropyPi` (`MultivariateDiffEntropy.lean:58`, 今 session 構築) に特化。`jointDifferentialEntropyPi_le_sum` (subadditivity, genuine 構造) が entropy 側足場。h 特化は signature 変更ゆえ新定理 restate (Phase 4)、旧版 deprecate。
- **Mathlib-shape 判断**: n-dim PL の結論形を multiplicative form `vol(λA+(1-λ)B) ≥ vol(A)^λ vol(B)^(1-λ)` に固定 (1D PL の結論形 `intF^λ*intG^(1-λ)≤intH` と同形、entropy power `exp((2/n)h)` に `Real.mul_rpow` で直結)。textbook additive form は `bm_additive_to_multiplicative` (genuine 既存) で派生。
