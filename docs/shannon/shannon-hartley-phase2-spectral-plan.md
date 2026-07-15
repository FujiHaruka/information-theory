# Shannon-Hartley Phase 2 — 時間帯域制限作用素のスペクトル理論 サブ計画 🌙

> **Parent**: [`shannon-hartley-operational-moonshot-plan.md`](shannon-hartley-operational-moonshot-plan.md) §Phase 2（prolate-DOF 壁核）
> **Inventory (SoT)**: [`shannon-hartley-phase2-spectral-inventory.md`](shannon-hartley-phase2-spectral-inventory.md)
> **関連**: [`whittaker-shannon-partial-moonshot-plan.md`](whittaker-shannon-partial-moonshot-plan.md)（sinc/sampling = CLOSED、kernel 資産）/ [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md)（`awgn_converse` = leg D 消費）

## 進捗

- [x] M0 在庫調査 ✅（`shannon-hartley-phase2-spectral-inventory.md`、3 GATING verdict 確定）
- [ ] Leg A — 作用素 + subspace + 自己共役 + 正 + `‖A‖≤1` 📋 **[genuine・first]**
- [ ] Leg B — コンパクト性（finite-rank kernel 極限）📋 **[big self-build・make-or-break]**
- [ ] Leg C — 固有値降順列挙 + 定性的 effective-rank 📋 **[self-build]**
- [ ] Leg D — `contAwgnMaxMessages_bddAbove` closure（Phase 3 leg 2）📋 **[de-risk payoff]**
- [ ] Leg E — tight concentration `prolate_eigenvalue_count`（LPS 壁）📋 **[irreducible wall・last]**

## ゴール / Approach

### Goal

親 §Phase 2 の壁核 `wall:nyquist-2w-dof` を **spectral theory で self-build** する。最終目標は 2 消費点:
(1) **Phase 3 achievability leg 2** `contAwgnMaxMessages_bddAbove`（`ShannonHartleyAchievability.lean:481`、現状
`@residual(wall:nyquist-2w-dof)`）を genuine に閉じる、(2) **Phase 4 main converse** `contAwgn_le_shannonHartley`
が消費する tight 固有値カウント `prolate_eigenvalue_count`。**(2) は irreducible な LPS 壁**、**(1) は (2) より
弱い定性的スペクトル構造で閉じる公算**（下記 中心問題 verdict）。

### Approach（解の全体形 — 作用素・スペクトル鎖・各消費点の接続）

`E := Lp ℂ 2 (volume : Measure ℝ)`（複素 Hilbert 空間、`CompleteSpace`✓）上に時間帯域制限作用素
`A := P_W ∘L Q_T ∘L P_W` を建てる。`Q_T` = `[0,T]` 本質時間制限射影、`P_W` = `[-W,W]` 帯域制限射影、
両者とも **閉部分空間への `starProjection`**（乗算作用素でなく射影として建てるのが Mathlib-shape-driven の要
— 自己共役・正が one-liner 化、inventory §D 設計勧告）。

スペクトル鎖（下流ほど深い）:

```
A = P_W Q_T P_W  (self-adjoint, positive, ‖A‖≤1)        ← Leg A（direct）
      │  compact（no Hilbert-Schmidt → finite-rank kernel 極限）
      ▼
IsCompactOperator A                                       ← Leg B（big self-build）
      │  structural spectral thm（eigenspaces span + 有限重複）
      ▼
prolateEigenvalues : ℕ → ℝ（降順）＋ #{k | λ_k>θ}<∞      ← Leg C（self-build）
      │                                     │
      │ 定性 effective-rank（compact 由来）  │ tight ≈2WT concentration（LPS）
      ▼                                     ▼
contAwgnMaxMessages_bddAbove（Phase 3 leg 2）   prolate_eigenvalue_count（Phase 4 converse）
      = Leg D（消費: awgn_converse + 有限次元回転） = Leg E（irreducible wall）
```

**各消費点の接続**:
- **Leg D → Phase 3**: `contAwgn_ge_shannonHartley`（`ShannonHartleyAchievability.lean:506`）が `le_csSup` で
  Leg D の `BddAbove` を消費（同一 file 内、親 plan leg 3）。Leg D が genuine 化すれば Phase 3 achievability
  closure が **LPS 壁 (Leg E) より前に** 着地しうる。
- **Leg E → Phase 4**: `contAwgn_le_shannonHartley`（Phase 4）が tight カウントを消費。ここだけ irreducible。

### route（次アクション）

**Leg A first**（direct one-liner、真の作用素 object を先に生む）→ **Leg B**（make-or-break の 500-900 行）→
**Leg C** → **Leg D**（Phase 3 payoff）→ **Leg E**（壁）。ただし Leg B 投資前に **Leg D の gateway atom**
（回転 + rank + Fano の還元 skeleton）を sorry-laden で先置きし「BddAbove が定性 effective-rank で閉じる」還元形を
先に固定する（下記 中心問題）。詳細 → 各 Leg 節。

---

## 中心問題 verdict — BddAbove は定性コンパクト性で閉じるか、tight カウントを要するか

**タスク指定の決定的問い**。親 plan + inventory + proof-pivot-advisor の 2026-07-15 audited verdict は
「leg 2 は `wall:nyquist-2w-dof` を共有」だが、finite-vs-exactly-2WT を分離していない。以下で分離する。

### verdict（証拠付き）

**BddAbove（leg 2）は tight concentration `prolate_eigenvalue_count`（LPS ≈2WT asymptotic）を要さない。
genuine コンパクト性（Leg B）＋ sampleCount `n` について一様な有限 effective-rank 境界（Leg C/D）で閉じる。
これは「作用素が bounded（`‖A‖≤1`）」より strictly 強く、tight ≈2WT concentration より strictly 弱い。tight
カウントは Phase 4 main converse（定数を EXACT に `W·log(1+P/(N₀W))` へ合わせる ≤ 方向）でのみ必要。**

### 決定的理由（reduction を trace）

`contAwgnMaxMessages = Nat.sSup {M | ∃ code, averageError ≤ ε}`（`ShannonHartleyOperational.lean:392`）。
`BddAbove` は **∃ 有限上界**（存在的有限性）— EXACT な値は不要。reduction:

1. **sample 基底の crude 境界は失敗**。per-letter `awgn_converse` は
   `I(msg;Y_1..Y_n) ≤ ∑_i (1/2)log(1+E[f(t_iᵢ)²]/(N₀/2))`。`log(1+x)≤x` + trace 回転不変で
   `I ≤ (1/N₀)·∑_i E[f(t_i)²]`。窓内電力 `∫_{[0,T]}f² ≤ TP` の Riemann 和で `∑_i E[f(t_i)²] ≲ nP` ⟹
   `I ≲ nP/N₀` = **`n` で発散**。`ContAwgnCode.sampleCount` は自由 ℕ（C4、oversampling 可）なので
   crude 有限上界は無い（親 plan 2026-07-15 の「crude・壁非依存」撤回は正当）。

2. **一様境界は effective-rank concentration を要する**。回転不変 MI
   `I ≤ (1/2)∑_k log(1+eig_k(Σ_s)/(N₀/2))`。`n` について一様に有限に抑えるには、固有値 `eig_k(Σ_s)` が
   **有限個 `D(W,T)` の mode を除き 0 近傍に集中**（= 有限 effective-rank）していることが要る。信号が
   `[-W,W]` 帯域制限 & `[0,T]` 本質時間制限ゆえ有効次元は `≈2WT` に留まる = 過剰標本が自由 DOF を生まない。

3. **その有限 effective-rank は「定性コンパクト性」で出る、LPS でない**。連続作用素 `A` がコンパクト ⟹
   固有値は 0 にのみ集積 ⟹ 任意閾値 `θ>0` に対し `#{k | λ_k(A)>θ}<∞`（有限）。有限標本作用素 `A_n`（√(T/n)
   正規化 sampling Gram）が `A_n → A`（作用素ノルム収束）ゆえ、`#{k | λ_k(A_n)>θ}` は `n` について
   一様に `#{k | λ_k(A)>θ/2}` 以下で bound。**これは compact + 収束の帰結であり、tight ≈2WT カウント
   (LPS) を要さない**。値は `D`（有限、`≈2WT` 近傍だが正確値不要）で十分。

4. **含意**: Legs B（compact）+ C（列挙 + 定性 rank）が genuine に着地すれば、**Leg D (BddAbove) は
   Phase 4 の LPS 壁 (Leg E) より前に閉じる** = Phase 3 achievability closure の major win。

### honest hedge + gateway atom + 撤退

- **これは 2026-07-15 audited verdict の refine（overturn でない）**: leg 2 は依然 `nyquist-2w-dof` **family**
  内（作用素のスペクトル構造を要する。auditor の「full-line↔window energy tie は band-limit/time-limit 構造が
  供給」と整合）。私の主張は「leg 2 が要する sub-object は compact + effective-rank であって LPS asymptotic
  ではない」。**コード側 SoT は Legs B/C/D が genuine 着地するまで leg 2 = `@residual(wall:nyquist-2w-dof)`
  のまま**（本 plan は prose に「壁でない」をキャッシュしない）。
- **gateway atom（Leg B 投資前に試す）**: 有限標本 sampling Gram の一様 frame bound `‖A_n‖≤1`（= [-W,W]
  帯域制限を rate `1/Δ≥2W` で標本化した √Δ-frame の Bessel bound 1、Poisson 和、**LPS でない**）+ 回転 +
  rank + Fano の還元 skeleton。これが「BddAbove が定性 effective-rank で閉じる」形を確定する。閉じないと
  判明したら verdict を訂正し leg 2 を素直に `wall:nyquist-2w-dof` 継続。
- **撤退**: Leg D の一様 effective-rank / frame bound が詰まれば honest `sorry + @residual(wall:nyquist-2w-dof)`
  （既 verdict へ fall back）。**BddAbove を `≥` 定理へ hyp 化 / 全直線エネルギー field 追加は禁止**（load-bearing
  tier-5、壁の偽装、下記 誠実性制約）。

---

## Leg A — 作用素 + subspace + 自己共役 + 正 + `‖A‖≤1` 📋 **[directly-available・first]**

**目的**: 真の作用素 object を建てる（下流全 Leg が参照）。proof-log: no（direct、短い）。**概算 120–200 行**。

**新 file**: `InformationTheory/Shannon/TimeBandLimiting.lean`（imports = inventory §Starting skeleton。
作成時 `InformationTheory.lean` に import 登録 = 実装 owner 担当）。`ShannonHartleyOperational.lean` は clean に保つ。

**signature スケッチ**（inventory decl + file:line）:

```lean
abbrev E : Type := Lp ℂ 2 (volume : Measure ℝ)
def timeLimitSubspace (T : ℝ) : Submodule ℂ E := …   -- 閉部分空間（real def、sorry 不可）
def bandLimitSubspace (W : ℝ) : Submodule ℂ E := …   -- 𝓕 で pull-back した閉部分空間（real def）
noncomputable def timeBandLimitingOp (T W : ℝ) : E →L[ℂ] E :=
  (bandLimitSubspace W).starProjection ∘L (timeLimitSubspace T).starProjection ∘L
    (bandLimitSubspace W).starProjection            -- Submodule.starProjection, Projection/Basic.lean:124
theorem timeBandLimitingOp_isSelfAdjoint (T W) : IsSelfAdjoint (timeBandLimitingOp T W)
  -- IsSelfAdjoint.conj_starProjection (Adjoint.lean:376) + isSelfAdjoint_starProjection (Adjoint.lean:371)
theorem timeBandLimitingOp_isPositive (T W) : (timeBandLimitingOp T W).IsPositive
  -- IsPositive.of_isStarProjection (Positive.lean:491) + IsPositive.adjoint_conj (Positive.lean:366)
theorem timeBandLimitingOp_norm_le_one (T W) : ‖timeBandLimitingOp T W‖ ≤ 1
  -- 射影ノルム ≤ 1 の合成（starProjection 3 段）
```

**再利用資産**: `MeasureTheory.Lp.fourierTransformₗᵢ`（LpSpace.lean:50、Plancherel 等距、`bandLimitSubspace`
定義に）+ `Lp.norm_fourier_eq`/`inner_fourier_eq`（LpSpace.lean:89/93）+ `HasOrthogonalProjection.ofCompleteSpace`。
**feasibility**: **(i) directly-available**（inventory §B/§C/§D、one-liner）。
**pitfall**: `bandLimitSubspace` の **閉性**（`𝓕`-then-restrict の連続性、`fourierTransformₗᵢ.continuous` +
指示関数 restrict の連続性）— 唯一の非自明部。`starProjection` は `HasOrthogonalProjection` を要し、それは
閉（= complete）部分空間でのみ供給される。
**循環チェック**: `timeBandLimitingOp T W` の `W` は物理帯域幅（作用素の入力）で DOF カウント `2W` ではない
（C3 ✓）。
**retreat line**: 閉性補題が Mathlib 不足で詰まれば当該補題を `sorry + @residual(wall:nyquist-2w-dof)`
（同 wall 集約、compound 化しない）。ただし **genuine 着地が期待値**。**def body（`timeLimitSubspace` 等）は
sorry 不可** — commit 前に real def（CLAUDE.md「sorry を書けない場合の扱い順」）。

---

## Leg B — コンパクト性 📋 **[self-buildable・make-or-break・最大リスク]**

**目的**: `IsCompactOperator (timeBandLimitingOp T W)`。Mathlib に Hilbert-Schmidt/Schatten 不在（inventory Q2、
loogle Found 0）ゆえ **finite-rank kernel 極限で self-build**。proof-log: yes。**概算 500–900 行**（Phase 2 の
line count の大半、zero scaffolding = 単独最大 feasibility リスク、inventory §Self-build #2）。

**signature スケッチ**:

```lean
theorem timeBandLimitingOp_isCompact (T W : ℝ) : IsCompactOperator (timeBandLimitingOp T W)
```

**構成**（inventory §A/§Self-build #2）: `B := P_W ∘L Q_T` として `A = B ∘L B†`、companion `B†B = Q_T P_W Q_T`
= `L²[0,T]` 上 kernel `k(s,t)=2W·sincN(2W(s−t))·𝟙_{[0,T]²}` の sinc 積分作用素（有限測度正方形上で bounded ⟹ L²）。
`A` と `B†B` は非零スペクトルを重複込みで共有 ⟹ `A` のコンパクト性は sinc 積分作用素に還元。
(a) kernel が L²、(b) simple function で L² 近似 → 各 simple kernel = finite-rank、(c) 作用素ノルム ≤ L²-kernel
ノルム（HS bound、inline 証明）、(d) `isCompactOperator_of_tendsto`（Compact/Basic.lean:459、`l=atTop` NeBot ✓）。

**再利用資産**: `isCompactOperator_of_tendsto`（Basic.lean:459）+ `isCompactOperator_id_iff_finiteDimensional`
（Compact/FiniteDimension.lean:26、finite-rank ⟹ compact）+ `IsCompactOperator.comp_clm/.clm_comp/.add/.smul`
（Basic.lean）+ `NormalizedSinc.sincN_int_eq_kronecker`（NormalizedSinc.lean:95）+ `integral_exp_boxcar_eq_sincN`
（WhittakerShannon.lean:63）+ `bandlimited_sup_bound`（ShannonHartleyOperational.lean:241、kernel boundedness）。
**feasibility**: **(ii) self-buildable on Mathlib**（壁でない、constructible）。ただし scaffolding 皆無。
**pitfall**: 「finite-rank ⟹ compact」は named lemma 不在（inventory §A）— `id_iff_finiteDimensional` + `comp_clm`
から ~20–40 行で自作。WS/sinc 固有関数で `A` を直接 finite-rank 近似する別ルートは Leg C 列挙と循環リスク →
**kernel-simple-function ルート推奨**（self-contained）。
**retreat line**: finite-rank 極限が予算内に詰まれば `sorry + @residual(wall:nyquist-2w-dof)`（親 plan 「詰まる
個別補題も同 wall に集約」）。**新 slug は禁止**（loogle-0 + two-stage + template 行数見積が揃わない限り）。
**degenerate fallback**: compact が予算内に self-build 不能なら Phase 2 を「Leg A genuine + Leg B/C/D/E を
`sorry @residual(wall:nyquist-2w-dof)`」に縮退（真の作用素 object は Phase 4 参照用に残る、単一集約壁）。
**hyp bundling は禁止**（compact/count を `*Hypothesis` predicate で渡す = tier-5 load-bearing）。

---

## Leg C — 固有値降順列挙 + 定性的 effective-rank 📋 **[self-buildable]**

**目的**: `prolateEigenvalues : ℕ → ℝ`（降順列挙）+ 「`#{k | λ_k>θ}<∞`（有限 effective-rank）」。proof-log: yes。
**概算 200–400 行**（inventory §Self-build #3）。

**signature スケッチ**:

```lean
noncomputable def prolateEigenvalues (T W : ℝ) : ℕ → ℝ := …   -- real def（spanning eigenspaces を降順列挙）
theorem prolateEigenvalues_antitone (T W) : Antitone (prolateEigenvalues T W)
theorem prolateEigenvalues_mem_Icc (T W) (n) : prolateEigenvalues T W n ∈ Set.Icc 0 1  -- ≥0 正、≤1 ‖A‖
theorem prolate_effectiveRank_finite (T W) (hθ : 0 < θ) :
    {n | θ < prolateEigenvalues T W n}.Finite                  -- ★ 定性 effective-rank（Leg D の核）
```

**構成**: `orthogonalComplement_iSup_eigenspaces_eq_bot`（Spectrum.lean:443、稠密 span）+
`finite_dimensional_eigenspace`（Spectrum.lean:463、有限重複）+ Fredholm
`IsCompactOperator.hasEigenvalue_iff_mem_spectrum`（FredholmAlternative.lean:220、非零 eig = 非零 spectrum）
→ 非零スペクトルは可算・0 のみ集積・各有限重複 ⟹ 重複込み降順列挙（0 で padding）。`∈[0,1]` は
`eigenvalue_nonneg_of_nonneg`（Spectrum.lean:409、正作用素）+ Leg A の `‖A‖≤1`。**`prolate_effectiveRank_finite`
は compact の帰結**（0 のみ集積 ⟹ `θ>0` 上に有限個）。
**feasibility**: **(ii) self-buildable on Mathlib**。降順 `ℕ→ℝ` 列は Mathlib 不在（finite-dim only、
`LinearMap.IsSymmetric.eigenvalues` Spectrum.lean:279）→ 自作 sorted list。
**pitfall**: 「0 に収束 / 0 から離れて離散」は Fredholm `antilipschitz_of_not_hasEigenvalue` 系を要する。
**循環チェック**: `prolateEigenvalues` は spectrum から定義（`2WT` は入力でない、C3 ✓）。`effectiveRank` は
`#{k | λ_k>θ}` で定義（`⌊2WT⌋` を def 入力にしない、C3 ✓）。
**retreat line**: 列挙 / effective-rank finiteness が詰まれば `sorry + @residual(wall:nyquist-2w-dof)`。
**def body（`prolateEigenvalues`）は sorry 不可** — real def。

---

## Leg D — `contAwgnMaxMessages_bddAbove` closure（Phase 3 leg 2）📋 **[de-risk payoff]**

**目的**: 既存 sorry `contAwgnMaxMessages_bddAbove`（`ShannonHartleyAchievability.lean:481`、現 `@residual(wall:
nyquist-2w-dof)`）を Legs B+C 経由で **genuine 化**。中心問題 verdict の実装 = 定性 effective-rank で BddAbove を
閉じる。proof-log: yes。**概算 250–500 行**。

**target signature**（既存、変更なし = signature ripple 無し）:

```lean
theorem contAwgnMaxMessages_bddAbove (T W N₀ P ε : ℝ)
    (hT : 0 < T) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) (hε0 : 0 < ε) (hε1 : ε < 1) :
    BddAbove { M : ℕ | ∃ c : ContAwgnCode T W P M, (c.averageError N₀).toReal ≤ ε }
```

**構成**（中心問題 verdict step 1–4 の実装）:
- **一様 frame bound（gateway atom）**: √(T/n)-正規化 sampling Gram `A_n` に `‖A_n‖≤1`（[-W,W] を `1/Δ≥2W` で
  標本化した Bessel bound、Poisson 和、LPS でない）。
- **有限次元回転**: 固定 `n` で `A_n` を対角化（`LinearMap.IsSymmetric.eigenvalues` Spectrum.lean:279、finite-dim
  で使用可）→ per-letter `awgn_converse`（既所有 genuine、AWGN）を回転後の effective mode に適用。
- **一様 effective-rank**: `A_n → A`（Leg B/C 由来）で `#{k | λ_k(A_n)>θ}` を `n` 一様に有限 `D` で bound
  （`prolate_effectiveRank_finite` 消費）→ `I ≤ D·(定数)` uniform ⟹ Fano で `M ≤` 有限 ⟹ `BddAbove`。
- **ℕ-sSup 罠**: unbounded `sSup` は junk `0`（親 plan、repo は `Cramer.lean`/`ParallelGaussian/PerCoord.lean`
  で既遭遇）→ `BddAbove` が `le_csSup`（leg 3）の前提。
**再利用資産**: Leg B `timeBandLimitingOp_isCompact` + Leg C `prolate_effectiveRank_finite` +
`awgn_converse`（AWGN）+ `parallel_gaussian_capacity_formula_minimal`（ParallelGaussian/PerCoordRegularity.lean:74、
有限次元回転の水充填形、参考）。
**feasibility**: **(ii) self-buildable — Legs B+C が genuine 着地する条件付き**。Leg B/C が壁化すれば Leg D も
transitive に壁。
**循環チェック**: サンプリング rate は achievability の構成選択で def 入力でない（C3 ✓）。BddAbove の core を
hyp 化しない（C1/C2 ✓）。
**retreat line**: 一様 frame/rank が詰まれば `sorry + @residual(wall:nyquist-2w-dof)`（2026-07-15 verdict へ fall
back）。**禁止**: `BddAbove` を `≥` 定理へ hyp 化、`ContAwgnCode` に全直線エネルギー field 追加（壁偽装）。
**consumer wiring**: `contAwgn_ge_shannonHartley`（`ShannonHartleyAchievability.lean:506`）が `le_csSup` で消費。
Leg D genuine 化で leg 3 も transitive に closure（tag は `plan:` のまま、Phase 3 assembly work）。

---

## Leg E — tight concentration `prolate_eigenvalue_count`（LPS 壁）📋 **[irreducible wall・last]**

**目的**: `#{n | 1/2 < prolateEigenvalues T W n}` の `⌊2WT⌋ + O(log WT)` 集中（Landau-Pollak-Slepian）。
**唯一の genuine irreducible 壁**。proof-log: yes（撤退 rationale）。Phase 4 main converse が消費。

**signature スケッチ**:

```lean
/-- 壁核: >1/2 の固有値カウント = ⌊2WT⌋ + O(log WT)（Landau-Pollak-Slepian）。 -/
theorem prolate_eigenvalue_count (T W : ℝ) (hT : 0 < T) (hW : 0 < W) :
    ⟨#{n | 1/2 < prolateEigenvalues T W n} と 2WT の集中不等式⟩ := by
  sorry   -- @residual(wall:nyquist-2w-dof)
```

**feasibility**: **(iii) genuine wall**（inventory §Walls、loogle `prolate`/`Slepian`/`Mercer` Found 0、
2026-07-14 確認）。self-build する asymptotic 資産が Mathlib 完全不在。
**循環チェック（最重要）**: `2WT` は本カウントの **結論** としてのみ現れる（`prolateEigenvalues` の def にも
`timeBandLimitingOp` の def にも `2W`/`⌊2WT⌋` は入らない、C3 ✓）。
**retreat line**: `sorry + @residual(wall:nyquist-2w-dof)`（sanctioned 撤退口）。**hyp bundling 禁止**
（concentration を `*Hypothesis` predicate で渡さない）。**statement は `True` placeholder でなく実不等式で書く**
（`prolateEigenvalues` 定義後、inventory §Starting skeleton の `True` は skeleton stand-in であり shippable でない）。

---

## 誠実性制約（explicit）

- **tight concentration `prolate_eigenvalue_count`（Leg E）= sanctioned `@residual(wall:nyquist-2w-dof)` 撤退口**。
  詰まらなければ genuine 化するが、詰まる公算が最も高い唯一の壁核。
- **load-bearing hyp bundling 禁止**: concentration / compact / BddAbove を `*Hypothesis`/`*Reduction`/`IsXxxClaim`
  predicate に束ねて仮説で渡さない。**`ContAwgnCode` に「全直線エネルギー field」を足して壁を回避しない**
  （窓外 sinc tail の抑制を field 化 = 壁偽装 tier-5）。**`≥` 定理へ `BddAbove` を hyp 化しない**。
- **compact（Leg B）は GENUINE か honest sorry の二択、fake 禁止**。degenerate 定義悪用 / `:True` slot も禁止。
- **Leg B/C/D が詰まった時の honest exit も `wall:nyquist-2w-dof`**（同一 family へ集約、compound 化しない）。
  **新 slug は** loogle-0 + two-stage conclusion-shape 検索 + template lemma 行数見積が揃った時のみ（CLAUDE.md
  「壁判定」）。
- **def body に sorry 不可**: `timeLimitSubspace`/`bandLimitSubspace`/`prolateEigenvalues` は commit 前に real def
  （CLAUDE.md「sorry を書けない場合の扱い順」、第一選択 = 定義を書き換えて sorry を proof body へ押し込む）。
- 実装 owner が新 sorry + `@residual` を commit したら **独立 honesty audit を同セッションで起動**（CLAUDE.md）。

---

## feasibility ledger（Leg 別、inventory 引用）

| Leg | target | 判定 | 根拠（inventory） |
|---|---|---|---|
| A | 作用素定義 | **directly-available** | `Lp.fourierTransformₗᵢ`（LpSpace.lean:50）+ `Submodule.starProjection`（Projection/Basic.lean:124）|
| A | 自己共役 | **directly-available** | `IsSelfAdjoint.conj_starProjection`（Adjoint.lean:376）one-liner |
| A | 正 | **directly-available** | `IsPositive.of_isStarProjection`（Positive.lean:491）+ `adjoint_conj`（Positive.lean:366）|
| A | `‖A‖≤1` | **directly-available** | 射影ノルム合成 |
| B | コンパクト性 | **self-buildable**（~500–900 行）| HS/Schatten 不在（Q2、Found 0）→ `isCompactOperator_of_tendsto`（Basic.lean:459）+ finite-rank sinc kernel 近似。**壁でない** |
| C | 固有値降順列挙 | **self-buildable**（~200–400 行）| 構造的 spectral thm `orthogonalComplement_iSup_eigenspaces_eq_bot`（Spectrum.lean:443）+ `finite_dimensional_eigenspace`（:463）+ Fredholm（:220）。降順 `ℕ→ℝ` 列は不在（finite-dim only :279）|
| C | 定性 effective-rank | **self-buildable** | compact の帰結（0 のみ集積 ⟹ `θ>0` 上有限）|
| D | `contAwgnMaxMessages_bddAbove` | **self-buildable（B+C 条件付き）** | 中心問題 verdict: 定性 effective-rank + 有限次元回転 + `awgn_converse`。tight カウント不要 |
| E | tight concentration | **genuine wall** | LPS asymptotic、Mathlib 完全不在（loogle `prolate`/`Slepian`/`Mercer` Found 0）|

---

## 循環チェック（C3 受入基準・全 Leg 集約）

**C3**: 定数 `2W`/`⌊2WT⌋` は **`prolate_eigenvalue_count`（Leg E）の結論としてのみ** 現れ、どの def の入力にも
現れない。確認:
- `timeBandLimitingOp T W` の `W` = 物理帯域幅（作用素入力）≠ DOF カウント `2W`。✓
- `prolateEigenvalues` = spectrum から定義、`2WT` 非入力。✓
- `prolate_effectiveRank_finite` = `#{k | λ_k>θ}` で定義、`⌊2WT⌋` 非入力。✓
- Leg D `BddAbove` = 定性有限 rank `D` で bound（EXACT `⌊2WT⌋` 不要）、code def をサンプルベクトルに制限しない
  （C1 維持）。✓
- Leg E で初めて `2WT` が **カウントの結論** として出る。✓
tell（循環兆候）: `contAwgn_eq_shannonHartley` が `rfl`/`unfold` のみ、`prolateEigenvalues` def に `2WT` 出現、
reduction が per-sample capacity をそのまま返す — いずれも本 plan の設計では発生しない。

---

## ripple / import

- **signature 変更なし**: Phase 2 は **新 file `TimeBandLimiting.lean` を ADD + closed 資産を read** のみ
  （inventory「no signature change to any existing shared InformationTheory lemma」）。Leg D は既存 sorry
  `contAwgnMaxMessages_bddAbove` を **fill**（signature 不変）→ `dep_consumers` blast-radius 不要。
- **consumer**: leg 2 `contAwgnMaxMessages_bddAbove` の消費者は同 file `contAwgn_ge_shannonHartley`
  （`ShannonHartleyAchievability.lean:506`、`le_csSup` 経由、親 plan leg 3）+ Phase 4 main converse（Leg E 経由）。
- **import cycle なし**: `TimeBandLimiting.lean` は Mathlib spectral/Fourier + `NormalizedSinc`/`WhittakerShannon`
  を import。`ShannonHartleyOperational`/`Achievability` は Leg D で `TimeBandLimiting` を import（逆向きなし、
  verified: Operational は spectral 資産を持たない）。作成時 `InformationTheory.lean` 登録 = 実装 owner。

---

## 判断ログ

append-only。決着済 entry は削除（git が履歴）、active な判断のみ（≤ 10 entry）。

1. **中心問題 verdict — BddAbove は tight カウントを要さない（refine、not overturn）**: leg 2 は定性コンパクト性
   （Leg B）+ 一様 effective-rank（Leg C/D）で閉じる。tight ≈2WT concentration（LPS、Leg E）は Phase 4 main
   converse 専用。2026-07-15 audited verdict は「nyquist-2w-dof family」までは正しく、私はその sub-object を
   compact+rank に特定（LPS asymptotic でない）。**コード side SoT は Legs B/C/D genuine 着地まで leg 2 =
   `@residual(wall:nyquist-2w-dof)` 維持**（prose に「壁でない」をキャッシュしない）。gateway atom（一様 frame
   bound `‖A_n‖≤1`）で還元形を先に固定。
2. **starProjection 設計（乗算作用素でない）**: `Q_T`/`P_W` を閉部分空間への `starProjection` で建てる
   （inventory §D 設計勧告）。自己共役 = `conj_starProjection`、正 = `of_isStarProjection` が one-liner 化。
   乗算作用素だと `M_g`-on-`Lp` API を自作させられる。
3. **Leg B（compact）が単独最大リスク**: HS/Schatten 皆無（Q2）ゆえ ~500–900 行 zero-scaffolding self-build。
   詰まれば `wall:nyquist-2w-dof` 集約（degenerate fallback = Leg A のみ genuine 残置）。kernel-simple-function
   ルート推奨（WS 固有関数直接近似は Leg C 循環リスク）。
4. **build order — Leg A first だが Leg D gateway atom を Leg B 前に先置き**: Leg A（direct、作用素 object）→
   Leg D の還元 skeleton（sorry-laden、BddAbove ← 定性 rank の形を確定）→ Leg B（make-or-break）→ C → D fill
   → E（壁）。2 feasibility unknown（compact self-build 可否 + BddAbove 還元形）を assembly より先に潰す。
