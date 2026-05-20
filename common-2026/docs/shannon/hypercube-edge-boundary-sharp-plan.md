# Hypercube edge-boundary entropy-sharp (B-2'') ムーンショット計画 🌙

> オーケストレータ指示: B-2' (`hypercube-edge-boundary-plan.md`, `Common2026/Shannon/HypercubeEdgeBoundary.lean`,
> 692 行, AM-GM 形 `2n|A|^{(n-1)/n} ≤ |∂_e A| + n|A|`) を起点に、
> **entropy-sharp 形** `|A| · (n - log₂ |A|) ≤ |∂_e A|` (Harper / Han / Cover-Thomas 17 流)
> を **条件付きエントロピー bridge** 経由で publish する。LW + AM-GM ではなく、
> `uniformOn A` 上で `H(X_i | X_{≠i})` を fibre size 1/2 の point-wise 計算で取り、
> chain rule + "conditioning reduces entropy" の 2 段で `Σ_i H(X_i|X_{≠i}) ≤ H(X) = log|A|`。
> 既存 counting identity `edgeBoundary_count_eq` (`Σ_i 2|π_{≠i}(A)| = n|A| + |∂_e A|`)
> を bridge に再利用、`Common2026/Shannon/HypercubeEdgeBoundary.lean` は touch しない。

## Status / 目標

> **実態整合 (2026-05-20): DONE-UNCOND (publish 済、0 sorry)** —
> 主結果 `edgeBoundary_entropy_sharp` (`Common2026/Shannon/HypercubeEdgeBoundarySharp.lean:627`) は
> 下記 signature と完全一致で実在、本体は genuine `by`-proof (pass-through なし)、`rg -nw sorry` 空振り。
> 条件付きエントロピー bridge 経路 (`condEntropy_coord_eq` 系) で discharge 済。plan 下記 Phase は完了扱い。

deferred `B-2''`. 主結果:

```lean
theorem edgeBoundary_entropy_sharp {n : ℕ} {A : Finset (Fin n → Bool)}
    (hA : A.Nonempty) :
    (A.card : ℝ) * ((n : ℝ) - Real.logb 2 A.card) ≤ (edgeBoundaryCount A : ℝ)
```

備考:
- **単位選択**: Lean は **nats** (`Real.negMulLog = -x · Real.log x`, `Real.log` = 自然対数) で
  entropy を扱う。target は `log₂ |A|` (`Real.logb 2`) で記述。bridge:
  `log|A| = (log 2) · logb 2 |A|`, つまり `log 2 · (n - logb 2 |A|) = n · log 2 - log|A|`。
- **`n = 0` ケース**: `Fin 0 → Bool` は単一点。`A.Nonempty` ⟹ `A.card = 1`、両辺 0。
- **整数差を `+` で回避するかの選択**: target は ℝ 上の差なので **そのまま不等式形** で書ける
  (B-2' の AM-GM 形のような整数差問題は **無い**)。

副目標:
- (Phase B) 核補題 `condEntropy_coord_eq`:
  `condEntropy μ_A (X_i) (X_{≠i}) = (2 · (|A| - |π_{≠i}(A)|) / |A|) · Real.log 2`,
  where `μ_A := uniformOn (A : Set (Fin n → Bool))`, `X_i ω := ω i`,
  `X_{≠i} ω := fun (j : {j // j ≠ i}) => ω j.val`.

## Approach

**Cover-Thomas / Madiman 流の conditional-entropy bridge** (textbook の素直な転写):

1. `μ_A := uniformOn (A : Set (Fin n → Bool))` を確率測度として固定。
   `Xs : Fin n → (Fin n → Bool) → Bool` を `Xs i ω := ω i`、
   `X_{-i} : (Fin n → Bool) → ({j // j ≠ i} → Bool)` を `fun ω j => ω j.val` で定義。
2. `entropy μ_A id = Real.log A.card` (既存 `entropy_uniformOn_eq_log_card`).
   `jointEntropy μ_A Xs = entropy μ_A id` (既存 LW の `h_joint_log` パターン).
3. **核補題** `condEntropy_coord_eq`:
   `condEntropy μ_A (Xs i) X_{-i} = (2 (|A| - |π_{≠i}(A)|) / |A|) · Real.log 2`.
   Pointwise 計算: 各 `y ∈ π_{≠i}(A)` で `condDistrib (Xs i) X_{-i} μ_A y` は
   `Bool` 上の measure で、fibre size に応じて Bern(1/2) (size 2) or Dirac (size 1)。
   negMulLog 和 = `log 2` or `0`。`μ_A.map X_{-i}` の y-mass は size/|A|。
4. **Chain rule + conditioning reduces entropy**:
   - chain rule (Han.lean): `jointEntropy μ_A Xs = Σ_i condEntropy μ_A (Xs i) (X_{< i})`
     where `X_{< i} ω := fun (j : Fin i.val) => Xs ⟨j.val, …⟩ ω`.
   - conditioning monotonicity (HanD.lean `condEntropy_subset_anti`):
     `Fin i.val` を `{j // j ≠ i}` に拡張 ⟹ `T₁ := prefix < i ⊆ T₂ := {j // j ≠ i}` で
     `condEntropy μ_A (Xs i) X_{-i} ≤ condEntropy μ_A (Xs i) X_{< i}`.
   - 合わせて `Σ_i condEntropy μ_A (Xs i) X_{-i} ≤ jointEntropy μ_A Xs = log|A|`.
5. **代数集計**: 3 の右辺を Σ で和取り
   `(2 log 2 / |A|) · Σ_i (|A| - |π_{≠i}(A)|) = (2 log 2 / |A|) · (n|A| - Σ_i |π_{≠i}(A)|)`。
   既存 `edgeBoundary_count_eq`: `2 Σ_i |π_{≠i}(A)| = n|A| + |∂_e A|`、
   即ち `n|A| - Σ_i |π_{≠i}(A)| = (n|A| - |∂_e A|)/2`. 代入で
   `Σ_i condEntropy ... = (log 2 / |A|) · (n|A| - |∂_e A|)`.
6. `(log 2 / |A|) · (n|A| - |∂_e A|) ≤ log|A|` を `|A|` 倍 + `log 2` 除して
   `n · log 2 - (|∂_e A| log 2 / |A|) ≤ log|A| / (1?)`... を logb 2 形に整える:
   `log|A| / log 2 = logb 2 |A|`. 結果: `|∂_e A| ≥ |A|(n - logb 2 |A|)`.

**Mathlib-shape-driven Definitions 節 (CLAUDE.md) の適用**:
- 主に reuse する Mathlib/Common2026 API:
  - `InformationTheory.Shannon.entropy` (`Common2026/Shannon/Bridge.lean:43`):
    `entropy μ Xs := ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})`。
    型クラス `[Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
    [MeasurableSingletonClass X]`. 自然対数形。
  - `InformationTheory.MeasureFano.condEntropy`
    (`Common2026/Fano/Measure.lean:68`):
    `condEntropy μ Xs Yo := ∫ y, ∑ x : X, Real.negMulLog
        ((condDistrib Xs Yo μ y).real {x}) ∂(μ.map Yo)`。
    型クラス `[MeasurableSpace Ω] [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y]
    [IsFiniteMeasure μ]`.
  - `jointEntropy_chain_rule` (`Common2026/Shannon/Han.lean:56`)
    n 変数 chain rule 既存。`X_{< i}` 形 (`fun ω (j : Fin i.val) => Xs ⟨j.val, …⟩ ω`)。
  - `condEntropy_subset_anti` (`Common2026/Shannon/HanD.lean:262`):
    `T₁ ⊆ T₂ ⟹ condEntropy μ (Xs i) (fun ω (j : T₂) => Xs j.val ω)
      ≤ condEntropy μ (Xs i) (fun ω (j : T₁) => Xs j.val ω)`。
- **shape 判断**:
  - 1 と 4 の条件付け側を **Finset 形** (`T : Finset (Fin n)`) で揃える方が
    `condEntropy_subset_anti` の signature と直結。`{j // j ≠ i}` ↔
    `Finset.univ.erase i` の reshape は既存 `jointEntropySubset_le_log_projectionExcept_card`
    (LoomisWhitney.lean) で `MeasurableEquiv.piCongrLeft` 経由のテンプレ確立済。
  - `X_{< i}` は `Fin i.val → α` 形 (`jointEntropy_chain_rule` の signature)。
    `Finset.univ.filter (· < i)` 形との reshape は HanD.lean
    `condEntropy_chainSummand_bridge` 既存 (180 行付近)。
  - **採用 shape**: 主補題 statement は **Finset 形** で書き、
    chain rule 適用時のみ `Fin i.val ≃ ↥(univ.filter (· < i))` reshape を呼ぶ。
- **textbook の Kernel / PMF 形は採用しない**: Mathlib に `condEntropy μ X Y` の
  汎用 def は **無く**, 本プロジェクトの `MeasureFano.condEntropy` (積分形)
  が唯一の既存定義。chain rule / monotonicity も全て本 def 上で publish 済み。
  Kernel 形に書き換える motivation なし。

## ファイル配置の判断

**判断**: **候補 B (新規 `Common2026/Shannon/HypercubeEdgeBoundarySharp.lean` 並立 publish)** を採用。

理由:
- B-2' (`HypercubeEdgeBoundary.lean`, 692 行) は **counting + LW + AM-GM** で完結、
  `uniformOn` / `condEntropy` / chain rule などの確率系 import を **持ち込んでいない**
  (`import Common2026.Shannon.LoomisWhitney` のみ)。
- B-2'' は `condEntropy` / `condEntropy_subset_anti` / `jointEntropy_chain_rule` を
  使うため、`Common2026.Shannon.HanD` + `Common2026.Shannon.LoomisWhitney`
  両方を import する必要がある。これを B-2' に追記すると **B-2' の依存表面が増えて
  上流 Mathlib PR 切り出し可能性が落ちる**。
- B-5 / B-5' / B-8 / B-8' の前例に倣う (新 file 並立)。
- 共有定義 (`flipCoord`, `projMap`, `extension`, `edgeBoundaryCount`,
  `internalEdgePairCount`, `projectionExcept`, `edgeBoundary_count_eq`,
  `internal_pair_count_eq_projection_sum`) は B-2' から **export されているのを
  そのまま import 経由で利用** (新規 namespace は作らない、
  `namespace InformationTheory.Shannon` 内に追加)。

**新規 file の冒頭 import 案**:

```lean
import Common2026.Shannon.HypercubeEdgeBoundary  -- B-2' counting identity 経由
import Common2026.Shannon.HanD                    -- condEntropy_subset_anti
import Common2026.Shannon.Han                     -- jointEntropy_chain_rule
import Common2026.Shannon.LoomisWhitney           -- uniformOn + entropy_uniformOn_eq_log_card
                                                  -- (HanD 経由で transitively 取れる場合は省略)
import Mathlib.Analysis.SpecialFunctions.Log.Base -- Real.logb 系
```

## Phase 0 — Mathlib API inventory 📋

**must-verify before skeleton**:

1. `InformationTheory.Shannon.entropy` full signature
   (`Common2026/Shannon/Bridge.lean:43`、verbatim):
   ```lean
   variable {Ω : Type*} [MeasurableSpace Ω]
   variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
     [MeasurableSpace X] [MeasurableSingletonClass X]
   noncomputable def entropy (μ : Measure Ω) (Xs : Ω → X) : ℝ :=
     ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})
   ```

2. `InformationTheory.MeasureFano.condEntropy`
   (`Common2026/Fano/Measure.lean:68`、verbatim):
   ```lean
   variable {Ω : Type*} [MeasurableSpace Ω]
   variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
     [MeasurableSpace X] [MeasurableSingletonClass X]
   variable {Y : Type*} [MeasurableSpace Y]
   def condEntropy (μ : Measure Ω) [IsFiniteMeasure μ]
       (Xs : Ω → X) (Yo : Ω → Y) : ℝ :=
     ∫ y, ∑ x : X, Real.negMulLog ((condDistrib Xs Yo μ y).real {x}) ∂(μ.map Yo)
   ```

3. `entropy_uniformOn_eq_log_card`
   (`Common2026/Shannon/LoomisWhitney.lean:46`、verbatim):
   ```lean
   theorem entropy_uniformOn_eq_log_card
       {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
       [MeasurableSpace β] [MeasurableSingletonClass β]
       {A : Finset β} (hA : A.Nonempty) :
       entropy (uniformOn (A : Set β)) (id : β → β) = Real.log A.card
   ```

4. `jointEntropy_chain_rule` (`Common2026/Shannon/Han.lean:56`、verbatim):
   ```lean
   variable {n : ℕ} {α : Type*}
     [Fintype α] [DecidableEq α] [Nonempty α]
     [MeasurableSpace α] [MeasurableSingletonClass α]
   variable {Ω : Type*} [MeasurableSpace Ω]
   theorem jointEntropy_chain_rule
       (μ : Measure Ω) [IsProbabilityMeasure μ]
       (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
       jointEntropy μ Xs
         = ∑ i : Fin n,
             InformationTheory.MeasureFano.condEntropy μ (Xs i)
               (fun ω (j : Fin i.val) =>
                 Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
   ```

5. `condEntropy_subset_anti` (`Common2026/Shannon/HanD.lean:262`、verbatim):
   ```lean
   theorem condEntropy_subset_anti
       (μ : Measure Ω) [IsProbabilityMeasure μ]
       (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
       (i : Fin n) {T₁ T₂ : Finset (Fin n)} (hT : T₁ ⊆ T₂) :
       InformationTheory.MeasureFano.condEntropy μ (Xs i)
           (fun ω (j : T₂) => Xs j.val ω)
         ≤ InformationTheory.MeasureFano.condEntropy μ (Xs i)
             (fun ω (j : T₁) => Xs j.val ω)
   ```

6. `Mathlib uniformOn` (`Mathlib.Probability.UniformOn`):
   - `uniformOn : Set α → Measure α` (本 PR 既存 import パス
     `Common2026/Shannon/LoomisWhitney.lean:2`).
   - `isProbabilityMeasure_uniformOn : (hf : s.Finite) → (h : s.Nonempty)
       → IsProbabilityMeasure (uniformOn s)`. (LW で使用済み)
   - `uniformOn_apply_finset` — Finset 形 で `(uniformOn ↑s) ↑t
       = (s ∩ t).card / s.card`. (LW で使用済み)

7. `condDistrib` (`Mathlib.Probability.Kernel.CondDistrib`):
   - `condDistrib Xs Yo μ : Kernel Y X`、`StandardBorelSpace X` (X = Bool で satisfied).
   - `compProd_map_condDistrib : (μ.map (Xs, Yo)) = (μ.map Xs) ⊗ₘ condDistrib Yo Xs μ`
     (`Common2026/Shannon/Entropy.lean:50` で使用済み)。
   - `condEntropy_coord_eq` の点別計算 (fibre Bern(1/2) or Dirac) のために,
     **`condDistrib (Xs i) X_{-i} μ_A y` の `Bool` 上の確率値** を
     `condDistrib_apply` (Mathlib `CondDistrib`) で `y`-fibre 上の積分形に展開する。
     **TBD**: 該当 lemma の signature を Phase 0 で **要 loogle 確認**
     (`loogle "condDistrib (_ ∘ _)" / "condDistrib _ _ _ _ {_} = _"`).

8. `Real.logb` (`Mathlib.Analysis.SpecialFunctions.Log.Base:43`):
   `noncomputable def logb (b x : ℝ) : ℝ := log x / log b`. (`log_div_log` で `rfl` 同値).

**TBD 一覧** (Phase 0 で要確認):
- (T0-a) `condDistrib_apply` の正確な shape (kernel value at `y` の積分形 vs 微分形).
- (T0-b) `μ_A.map X_{-i}` の y-mass が `|fibre|/|A|` になることを既存
  `uniformOn_apply_finset` から最短ルートで取れるか, それとも 1 段の helper lemma
  (`uniformOn_map_proj_apply`) を新規 publish するか.
- (T0-c) Bool 上の `negMulLog (1/2) + negMulLog (1/2) = log 2` は
  `Real.negMulLog` の代数 + `Real.log_half` (`Real.log_inv 2 = -log 2`) で済むか.

## Phase A — uniformOn 確率測度上の skeleton statements 📋

新規 `Common2026/Shannon/HypercubeEdgeBoundarySharp.lean` の **skeleton** (全て `:= by sorry`):

```lean
namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

/-! ## Phase A — μ_A setup helpers -/

/-- `μ_A := uniformOn (A : Set (Fin n → Bool))`、`A.Nonempty` で確率測度。 -/
private lemma uniformOn_A_isProb
    {n : ℕ} {A : Finset (Fin n → Bool)} (hA : A.Nonempty) :
    IsProbabilityMeasure (uniformOn (A : Set (Fin n → Bool))) := by sorry

/-- `Xs i ω := ω i` の measurability。`measurable_pi_apply` の薄いラッパー。 -/
private lemma xsCoord_measurable {n : ℕ} (i : Fin n) :
    Measurable (fun ω : Fin n → Bool => ω i) := by sorry

/-- `X_{-i} ω j := ω j.val` (`{j // j ≠ i} → Bool` 値) の measurability。 -/
private lemma xExceptCoord_measurable {n : ℕ} (i : Fin n) :
    Measurable (fun ω : Fin n → Bool => fun (j : {j : Fin n // j ≠ i}) => ω j.val) :=
  by sorry

/-- `μ_A.map (Xs_full) = μ_A` (id reshape, B-2' AM-GM の `h_joint_log` パターン). -/
private lemma jointEntropy_xs_eq_log_card
    {n : ℕ} {A : Finset (Fin n → Bool)} (hA : A.Nonempty) :
    jointEntropy (uniformOn (A : Set (Fin n → Bool)))
        (fun (i : Fin n) (ω : Fin n → Bool) => ω i)
      = Real.log A.card := by sorry
```

## Phase B — 核補題 `condEntropy_coord_eq` 📋

核 (`H(X_i | X_{≠i}) = (2 (|A| - |π_{≠i}(A)|) / |A|) · log 2`) を 3 段で:

```lean
/-- direction `i` における doubly-covered fibre 数。 -/
private noncomputable def doublyCoveredCount
    {n : ℕ} (i : Fin n) (A : Finset (Fin n → Bool)) : ℕ :=
  A.card - (projectionExcept i A).card

/-- 各 `y ∈ projectionExcept i A` で fibre size c_i(y) ∈ {1, 2}、
size 2 の y 数 = doublyCoveredCount i A。 -/
private lemma fibre_size_classification
    {n : ℕ} (i : Fin n) {A : Finset (Fin n → Bool)} :
    (projectionExcept i A).filter (fun y =>
        (A.filter (fun x => projMap i x = y)).card = 2)
      |>.card = doublyCoveredCount i A := by sorry

/-- 各 `y ∈ proj` の `condDistrib (Xs i) X_{-i} μ_A y` 上の Shannon エントロピー:
size-2 fibre ⟹ `log 2`、size-1 fibre ⟹ `0`. -/
private lemma pointwise_condEntropy_value
    {n : ℕ} (i : Fin n) {A : Finset (Fin n → Bool)} (hA : A.Nonempty)
    (y : {j : Fin n // j ≠ i} → Bool) (hy : y ∈ projectionExcept i A) :
    ∑ b : Bool, Real.negMulLog
        ((condDistrib (fun ω : Fin n → Bool => ω i)
            (fun ω j => ω j.val) (uniformOn (A : Set _)) y).real {b})
      = if (A.filter (fun x => projMap i x = y)).card = 2 then Real.log 2 else 0 :=
  by sorry

/-- 核補題: direction `i` の `condEntropy`。 -/
theorem condEntropy_coord_eq
    {n : ℕ} {A : Finset (Fin n → Bool)} (hA : A.Nonempty) (i : Fin n) :
    InformationTheory.MeasureFano.condEntropy
        (uniformOn (A : Set (Fin n → Bool)))
        (fun ω => ω i)
        (fun ω (j : {j : Fin n // j ≠ i}) => ω j.val)
      = (2 * ((A.card : ℝ) - ((projectionExcept i A).card : ℝ)) / A.card) * Real.log 2 :=
  by sorry
```

**証明戦略**:
- `condEntropy` def の積分を `μ_A.map X_{-i}` 上に展開、`integral_fintype` で
  `Σ_y P(X_{-i}=y) · (内側 negMulLog 和)` に reshape。
- `μ_A.map X_{-i} {y}` は y-fibre size / |A|:
  - `y ∈ proj` で fibre size = 1 → mass = 1/|A|
  - `y ∈ proj` で fibre size = 2 → mass = 2/|A|
  - `y ∉ proj` → mass = 0
- 内側和 (`pointwise_condEntropy_value`): size-1 のとき Dirac → 0; size-2 のとき Bern(1/2) → log 2。
- Σ = (size-2 fibre 数) · (2/|A|) · log 2 = 2 D_i / |A| · log 2.
- D_i = |A| - |π_{≠i}(A)| (B-2' Phase A の判断ログ #3 で確立済み identity).

## Phase C — 反例なし、chain rule + monotonicity 適用 📋

```lean
/-- chain rule + conditioning reduces entropy で `Σ_i condEntropy_coord_eq` を log|A| で
押さえる。
key: `Fin i.val ↪ {j // j ≠ i}` の Finset 包含
`(Finset.univ.filter (· < i)) ⊆ (Finset.univ.erase i)` で `condEntropy_subset_anti`。 -/
theorem sum_condEntropy_le_log_card
    {n : ℕ} {A : Finset (Fin n → Bool)} (hA : A.Nonempty) :
    ∑ i : Fin n,
        InformationTheory.MeasureFano.condEntropy
          (uniformOn (A : Set (Fin n → Bool)))
          (fun ω => ω i)
          (fun ω (j : {j : Fin n // j ≠ i}) => ω j.val)
      ≤ Real.log A.card := by sorry
```

**証明戦略**:
- `jointEntropy_chain_rule` で `log|A| = Σ_i condEntropy μ_A (Xs i) X_{<i}`。
- 各 `i` で `condEntropy_subset_anti` を `T₁ := univ.filter (· < i)`,
  `T₂ := univ.erase i` に適用 (`T₁ ⊆ T₂` は `Finset.subset_iff` + 場合分け).
- `X_{<i}` (`Fin i.val → Bool`) と `X_{T₁}` (`↥(univ.filter (· < i)) → Bool`) は
  reshape (`MeasurableEquiv.piCongrLeft`, `condEntropy_measurableEquiv_comp`、HanD.lean
  `condEntropy_chainSummand_bridge` パターン)。
- `X_{T₂}` (`↥(univ.erase i) → Bool`) と `X_{-i}` (`{j // j ≠ i} → Bool`) も
  同様に reshape。
- 結果: 各 `i` で `condEntropy ... X_{-i} ≤ condEntropy ... X_{<i}`,
  Σ で `Σ_i condEntropy_coord ≤ Σ_i chain-rule summand = log|A|`.

## Phase D — 主定理組み立て 📋

```lean
/-- B-2'' 主結果 (Harper / Han entropy-sharp edge isoperimetric)。 -/
theorem edgeBoundary_entropy_sharp {n : ℕ} {A : Finset (Fin n → Bool)}
    (hA : A.Nonempty) :
    (A.card : ℝ) * ((n : ℝ) - Real.logb 2 A.card) ≤ (edgeBoundaryCount A : ℝ) := by
  sorry
```

**証明戦略**:
- Phase B (`condEntropy_coord_eq`) と Phase C (`sum_condEntropy_le_log_card`)
  を合成: `Σ_i (2 (|A| - |π_{≠i}|) / |A|) · log 2 ≤ log|A|`.
- LHS を `(2 log 2 / |A|) · (n|A| - Σ_i |π_{≠i}|)` に。
- `edgeBoundary_count_eq` を **ℝ 上 cast** で
  `2 · Σ_i |π_{≠i}| = (n|A| : ℝ) + (|∂_e A| : ℝ)`,
  即ち `Σ_i |π_{≠i}| = (n|A| + |∂_e A|)/2` ⟹ `n|A| - Σ_i |π_{≠i}| = (n|A| - |∂_e A|)/2`.
- 代入: `(log 2 / |A|) · (n|A| - |∂_e A|) ≤ log|A|`.
- `Real.logb 2 = log / log 2` (`Real.logb` 定義) で
  `(n - logb 2 |A|) · log 2 = n · log 2 - log|A|` に置換。
- 両辺 `|A|` 倍 + `log 2` (正) 除で `|A|(n - logb 2 |A|) ≤ |∂_e A|`.
- **`n = 0` ケース**: `A.card = 1` (Bool^0 の `Nonempty` Finset)、
  `logb 2 1 = 0`、`edgeBoundaryCount = 0`、両辺 0、`le_refl`。
- **`log 2 > 0`** は `Real.log_pos (by norm_num : (1 : ℝ) < 2)`.
- 代数最後の段は `linarith` または `nlinarith` (B-5' でのテンプレ).

## 見積行数 / 検証条件

- **行数見積**: 200–280 行 (Phase A helpers 30 行 + Phase B 核 100–140 行
  [fibre 分類 + pointwise condDistrib 計算が最大の重み] + Phase C 60–80 行
  [chain rule reshape + subset_anti 2 回 reshape] + Phase D 20–30 行).
- seeds の言い値「~80–120 行」は **B-2' の counting identity を再利用済み**
  と前提しており妥当だが, fibre size の condDistrib 値計算 (Phase B) の
  Mathlib API 経路次第で +50 行の見込み。
- **検証**: `lake env lean Common2026/Shannon/HypercubeEdgeBoundarySharp.lean`
  silent (0 sorry / 0 error / 0 warning).
- `Common2026.lean` に
  `import Common2026.Shannon.HypercubeEdgeBoundarySharp` 追記。

## 判断ログ

1. **ファイル配置 (候補 A vs B)**: **候補 B** 採用 (新規 `HypercubeEdgeBoundarySharp.lean`)。
   B-2' (`HypercubeEdgeBoundary.lean`) の依存表面 (`LoomisWhitney` のみ) を保護し、
   `HanD.condEntropy_subset_anti` / `Han.jointEntropy_chain_rule` 依存を B-2'' 側に局所化。
   B-5 / B-5' / B-8 / B-8' の並立 publish 前例に整合。
2. **単位選択 (nats vs bits)**: **internal は nats** (`Real.negMulLog` = 自然対数)、
   **statement は `Real.logb 2`** で publish。bridge は `Real.logb` 定義
   (`log / log 2`) で素朴に処理 (`Real.log_pos (1 < 2)` で除去可能).
3. **condEntropy shape 選択**: 既存 `InformationTheory.MeasureFano.condEntropy`
   (積分形, `Common2026/Fano/Measure.lean:68`) を採用。Mathlib に汎用 `condEntropy`
   は無く, 本プロジェクトの def が唯一の selection。Kernel 形に書き換える motivation なし。
4. **条件付け index reshape**: `Fin i.val ↪ univ.filter (· < i) ↪ univ.erase i ↪ {j // j ≠ i}`
   の 3 段 reshape を許容。各段で `MeasurableEquiv.piCongrLeft` +
   `condEntropy_measurableEquiv_comp` (HanD.lean に既存テンプレ) を呼び、
   reshape 自体が **proof の半分以上** を占める見込み (Phase C ~60–80 行)。
5. **integer 差を `+` で回避するか**: target が ℝ 上の不等式なので **不要**。
   B-2' の AM-GM 形 `2n|A|^{(n-1)/n} ≤ |∂_e A| + n|A|` は ℕ 差を避けるため `+` 形にしたが、
   B-2'' は **直接** `|A|(n - logb 2 |A|) ≤ |∂_e A|` で書ける。
6. **`fibre_size_classification` の必要性**: Phase B-(b) の `pointwise_condEntropy_value`
   の中で `(A.filter ...).card = 2 / 1` の場合分けで分岐するため、
   `if-then-else` 形 (整数 fibre size に基づく) を介すと case split が 1 段で済む。
   B-2' の `h_per_y` (HypercubeEdgeBoundary.lean:302) と同様の 4-case 結合は **不要**
   (Phase C の subset_anti が "条件包含 → 単調" を取るので, `(2|A| - 2|π_{≠i}|)/|A|·log 2`
   の Σ 形だけ取れれば十分).

## risk / fallback

- **R1 (大)**: `condDistrib (Xs i) X_{-i} μ_A y` の `Bool` 上の `real` 値
  (`(μ_A.map X_{-i})`-a.e. の y で `Bern(1/2)` or `Dirac`) を解析計算する Mathlib lemma
  が直接見当たらない場合。
  - **fallback**: `compProd_map_condDistrib` で `μ_A.map ((Xs i), X_{-i}) =
    (μ_A.map X_{-i}) ⊗ₘ condDistrib (Xs i) X_{-i} μ_A` を取り、
    両辺の `({b} × {y})` mass を `Measure.compProd_apply_prod` で比較して
    `condDistrib y {b}` を **間接定義式** で取り出す (Phase A `entropy_pair_eq_entropy_add_condEntropy`,
    `Common2026/Shannon/Entropy.lean:41` の `h_pair_real` パターン)。
- **R2 (中)**: chain rule の summand `condEntropy μ (Xs i) (X_{< i})` と
  `condEntropy_subset_anti` の `condEntropy μ (Xs i) (X_{T₁ : Finset})` の
  reshape (`Fin i.val ≃ ↥(univ.filter (· < i))`) が HanD.lean
  `condEntropy_chainSummand_bridge` (`Common2026/Shannon/HanD.lean:83`) の
  逆向きで使えない場合。
  - **fallback**: HanD.lean の private lemma を public 化 (or 写経) +
    `{j // j ≠ i}` ↔ `↥(univ.erase i)` の equiv を新規 publish (B-2' Phase A の
    `idx : ↥(univ.filter (· ≠ i)) ≃ {j : Fin n // j ≠ i}` パターン).
- **R3 (小)**: `n = 0` 単一点ケースで `Fin 0 → Bool` 上の `condEntropy` /
  `condDistrib` が degenerate. `A.card = 1` ケースで `logb 2 1 = 0` も合わせて
  early return が必要かもしれない。
  - **fallback**: `by_cases hn : n = 0` で先頭分岐 (B-2' の
    `sum_projection_card_ge_amgm` パターン, `HypercubeEdgeBoundary.lean:608`).
