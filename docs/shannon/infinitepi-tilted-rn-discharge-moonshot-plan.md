# infinitePi-tilted RN discharge ムーンショット計画 🌙 (T1-C Cramér Phase C + Chernoff converse 同根 frontier)

**Status**: CLOSED ✅ (2026-05-20) — Phase 1-4 全達成。詳細は下の実態整合ブロック。

> 実態整合 (2026-05-20): **DONE — Phase 1-4 全達成、当初の「最低保証」を大きく超過**。進捗ブロックと
> 判断ログが起草時のまま (Phase 0-V 全 [ ]、判断ログは起草 2 件のみ) で **重度に陳腐化**。実態:
> - Phase 1 本丸 `pi_tilted_sum_eq_pi_tilted` ✅ `InformationTheory/Shannon/MeasurePiTiltedFactorization.lean:121`
>   (0 sorry、独立 module 化も判断どおり)。fintype 版 `pi_tilted_sum_eq_pi_tilted_fintype` も
>   `InfinitePiTiltedChangeOfMeasure.lean:106`。
> - Phase 2-3 cylinder lift + change-of-measure ✅ `InfinitePiTiltedChangeOfMeasure.lean`:
>   `infinitePi_partialSum_event_eq_pi` (:139)、`change_of_measure_lower_bound_pi` (:189)。
> - Phase 4 ✅ residual predicate `IsTiltedWindowEventuallyLarge` (:282) + reduction
>   `isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge` (:293) + `cramer_lower_phaseC_residual_discharge`
>   (:361)。interior ケースは `tiltedWindow_eventually_large_of_interior` (:463) で discharge。W-3 撤退
>   (residual 縮約) どおり着地。**boundary ケースの CLT closure は ✅ 達成 (2026-06-11)**: 子
>   `cramer-chernoff-clt-closure` plan が `InformationTheory/Shannon/CramerCltBoundaryClosure.lean`
>   (0 sorry, sorryAx-free, 監査 PASS) に headline `cramer_lower_boundary_unconditional` を publish
>   (内部最適 tilt `a = deriv cgf lam` で residual largeness hyp 除去)。子判断ログ #4 / `05ed225`。
> - ✅ **配線完了 (2026-06-11, 判断ログ #26 / 子 `cramer-root-wiring-plan.md`)**: 上の closed-but-unwired
>   状態を解消。`cramer_lower_phaseC_partial_discharge` (root A) は 8 decl を新上流 `CramerBoundaryUpstream.lean`
>   へ hoist して import cycle を解消 → `exact cramer_lower_boundary_unconditional` で discharge。一般 iid
>   `cramer_lower` (root B) は新下流 `CramerGeneralLower.lean` へ移設 → iid joint law transport で headline へ
>   落として discharge。両 root **sorryAx-free** (独立監査 `@audit:ok`、`8a8a001`)。project 実 sorry 17→15。

<!--
雛形メモ (moonshot-plan-template.md より):
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 削除/廃止された Phase は ~~取り消し線~~ で残す（完全削除しない、過去参照のため）
- 判断ログは append-only。Phase 中の方針変更・撤退・当初仮定の修正を記録
- `rg "^- \[ \]"` で残タスク横断 grep、`rg "🔄"` でピボット箇所だけ拾える
-->

> **Predecessor (inventory)**: [`infinitepi-tilted-rn-discharge-mathlib-inventory.md`](infinitepi-tilted-rn-discharge-mathlib-inventory.md) — verdict (b)/(c) 境界、鍵 lemma 列挙済 (`tilted_mul_apply_cgf`, `infinitePi_cylinder`, `setLIntegral_rnDeriv`, `iIndepFun.cgf_sum`, E 行 `Found 0` 群)。
>
> **Related parents**:
> - [`cramer-lc2-discharge-moonshot-plan.md`](cramer-lc2-discharge-moonshot-plan.md) §撤退ライン L-D3 (Phase A plumbing publish 済)
> - [`cramer-lc2-ext-moonshot-plan.md`](cramer-lc2-ext-moonshot-plan.md) §Approach (tilted LLN B-1/B-3 publish 済)
> - [`chernoff-converse-moonshot-plan.md`](chernoff-converse-moonshot-plan.md) (Chernoff 側 `IsBayesErrorPerTiltLowerBound`)
>
> **Sub-plan (後継 / 子)**:
> - [`cramer-chernoff-clt-closure-moonshot-plan.md`](cramer-chernoff-clt-closure-moonshot-plan.md) §撤退ライン W-3 boundary CLT closure (residual predicate の境界ケース `a = m = deriv cgf lam` を CLT で実証する上振れ復帰 plan。consumer root の def-fix は 2026-06-11 完了 = 判断ログ #24)
>
> **対象 gap (frontier 最深)**: `InformationTheory/Shannon/Cramer/LC2PhaseC.lean:102` の pass-through 述語
>
> ```lean
> def IsMeasureInfinitePiTiltedEq (μ₀ : Measure Ω₀) (Y : Ω₀ → ℝ) (lam : ℝ) : Prop :=
>   ∀ a ε : ℝ, 0 < ε → ∃ C > 0, ∀ᶠ n : ℕ in atTop,
>       C * Real.exp (-(n:ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε))
>         ≤ (Measure.infinitePi (fun _ : ℕ => μ₀)).real
>             {ω : ℕ → Ω₀ | (a:ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)}
> ```
>
> 数学核心: tilted 無限積 `Measure.infinitePi (fun _ => μ₀.tilted (lam·Y·))` の width-n cylinder 上 RN 微分 = `exp(lam·∑Y(ωᵢ) − n·Λ(lam))`。
>
> **現実的スコープ (確定済)**: full 0-sorry はマルチセッション PR 級。本計画の**第一目標 = 「足りない 1 ピース」= 有限 `Measure.pi` tilt 因子分解補題を 0-sorry で完全に建てること** (Phase 1)。`IsMeasureInfinitePiTiltedEq` 全体がセッション内で閉じない場合、**sorry を残さず** strictly smaller residual predicate へ縮約する (撤退ライン = predicate 化、sorry 化ではない)。
>
> **no-sorry 規約厳守**: 全 committed 補題は 0-sorry。最低保証 deliverable = 有限 tilt 因子分解補題 (Phase 1) が 0-sorry で立つこと。

## 進捗

- [ ] Phase 0 — 在庫差分再確認 (本計画起草時に loogle 再裏取り済、§Phase 0) ✅
- [ ] Phase 1 — **有限 `Measure.pi` tilt 因子分解補題群 (本丸・最優先・0-sorry 必達)** 📋 ← [inventory §自作 1](infinitepi-tilted-rn-discharge-mathlib-inventory.md)
- [ ] Phase 2 — cylinder lift (`infinitePi_cylinder` で width-n cylinder へ持ち上げ) 📋
- [ ] Phase 3 — change-of-measure + 既存 tilted LLN 合流 📋
- [ ] Phase 4 — `IsMeasureInfinitePiTiltedEq` discharge **or** residual predicate 縮約 📋
- [ ] Phase V — verify + 親 plan 状態反映 📋

**今セッション到達見込み (率直マーキング)**: Phase 0 (済) + **Phase 1 が本セッションのゲート**。Phase 1 が割れれば Phase 2 へ着手するが、Phase 2-3-4 までフル到達は楽観シナリオ。**現実的には本セッション = Phase 1 完遂 + Phase 2 着手** が中央値。Phase 4 full discharge は次セッション以降。

## ゴール / Approach

### Goal (最終定理)

`CramerLC2PhaseC.IsMeasureInfinitePiTiltedEq μ₀ Y lam` を bounded measurable `Y` + `0 ≤ lam` で 0-sorry に満たし、`cramer_lower_phaseC_partial_discharge` 系の `h_pred` 引数を削除した完全形 wrapper を publish する。最低保証は Phase 1 の有限因子分解補題単独 publish。

### Approach (overall strategy / shape of solution)

**全体パイプライン**:

```
┌─────────────────────────────────────────────────────────────────────────┐
│ Phase 1 (本丸): 有限 Measure.pi tilt 因子分解                              │
│   pi_tilted_sum_eq_pi_tilted :                                            │
│     (Measure.pi (fun _ : Fin n => μ₀)).tilted (fun x => ∑ i, lam·Y (x i)) │
│       = Measure.pi (fun _ : Fin n => μ₀.tilted (lam·Y·))                  │
│   ── 証明武器: Measure.pi_eq (box 上一致 ⇒ 測度一致) ──                    │
└─────────────────────────────────────────────────────────────────────────┘
                              ↓ (有限版が確立)
┌─────────────────────────────────────────────────────────────────────────┐
│ Phase 2: cylinder lift                                                    │
│   width-n event {ω | a·n ≤ ∑_{i<n} Y(ωᵢ)} は range n の cylinder。       │
│   infinitePi_cylinder / infinitePi_eq_pi で                              │
│     (infinitePi (fun _:ℕ => μ₀.tilted ...)).real (cylinder)              │
│       = (Measure.pi (fun _:Fin n => μ₀.tilted ...)).real (...)           │
│   両側 (tilted ambient / un-tilted ambient) で cylinder ↔ Fin n pi 化。   │
└─────────────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────────────┐
│ Phase 3: change-of-measure + LLN 合流                                     │
│   Phase 1 の有限因子分解 + tilted_apply' / setLIntegral_rnDeriv で         │
│   un-tilted pi 上の event 質量を tilted pi 上の積分に書き換え:            │
│     (pi μ₀).real E_n ≥ exp(-n(λa-Λ(λ)+λε)) · (pi μ₀.tilted ...).real E_n' │
│   E_n' := {|S̄_n - a| < ε} に絞り、CramerLC2DischargeExt の              │
│   tilted_lln_in_probability_real で (pi tilt).real E_n' → 1 を合流。      │
└─────────────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────────────┐
│ Phase 4: IsMeasureInfinitePiTiltedEq discharge                           │
│   ∀ a ε, ∃ C, ∀ᶠ n の形に C := 1/2 を入れて閉じる。                       │
│   ── 閉じない場合 → residual predicate 縮約 (§撤退ライン) ──              │
└─────────────────────────────────────────────────────────────────────────┘
```

#### Phase 1 (本丸) の証明戦略 — 具体

**Mathlib-shape-driven** (CLAUDE.md): 因子分解補題は `Measure.pi_eq` の conclusion form (`Measure.pi μ = μ'` ⇐ box 上一致) に乗せる形で定義する。在庫の E 行で確認した通り `Measure.pi × withDensity` / `Measure.pi × tilted` の collapse は **`Found 0`** (本計画起草時に loogle で再裏取り)。よって以下の素材で **自前構築**:

1. **uniqueness 武器** — `Measure.pi_eq` (`Mathlib/MeasureTheory/Constructions/Pi.lean:281`):
   ```lean
   theorem pi_eq [∀ i, SigmaFinite (μ i)] {μ' : Measure (∀ i, α i)}
       (h : ∀ s : ∀ i, Set (α i), (∀ i, MeasurableSet (s i)) →
            μ' (pi univ s) = ∏ i, μ i (s i)) :
       Measure.pi μ = μ'
   ```
   `μ' := (Measure.pi μ₀).tilted (∑ lam·Y∘eval)` と置き、box `pi univ s` 上で
   `μ' (pi univ s) = ∏ i, (μ₀.tilted (lam·Y·)) (s i)` を示せば因子分解が確定。
   `[∀ i, SigmaFinite ...]` は `IsProbabilityMeasure μ₀` から自動 (有限測度 ⇒ SigmaFinite)。

2. **左辺 box 質量** — `tilted_apply'` (`Tilted.lean:101`, measurable set 版):
   ```lean
   lemma tilted_apply' (μ : Measure α) (f : α → ℝ) {s : Set α} (hs : MeasurableSet s) :
       μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal (exp (f a) / ∫ x, exp (f x) ∂μ) ∂μ
   ```
   `μ := Measure.pi μ₀`, `f := fun x => ∑ i, lam·Y (x i)`, `s := pi univ s`。
   - 分子 `exp(∑ i, lam·Y (x i)) = ∏ i, exp(lam·Y (x i))` (`Real.exp_sum`)。
   - 分母正規化 `∫ x, exp(∑ lam·Y (x i)) ∂(pi μ₀) = ∏ i, ∫ exp(lam·Y) ∂μ₀ = (∫ exp(lam·Y) ∂μ₀)^n`
     (product 上の積分 = ∏ marginal、`integral_pi` / `lintegral` 因子化)。
   - 結果 box 上 lintegrand は **∏ of per-coord density** に分解。

3. **product Tonelli (★ 自前の核)** — `∫⁻ over (pi μ₀) of (∏ i, gᵢ(x i)) restricted to box = ∏ i, ∫⁻_{sᵢ} gᵢ ∂μ₀`。
   在庫 E 行 + 本計画起草時 loogle で `lintegral_pi` 直接形は **不在** (Sobolev の `lintegral_prod_lintegral_pow_le` のみ hit、これは不等式で不使用)。
   **構築経路 (2 択、Phase 1-1 で確定)**:
   - **経路 (a) — 各座標 withDensity 化して再 `pi_pi`**: 因子分解の右辺を先に
     `Measure.pi (fun _ => μ₀.tilted (lam·Y·))` と置き、その box 質量を `pi_pi`
     (`Pi.lean:293`, `Measure.pi μ (pi univ s) = ∏ i, μ i (s i)`) で
     `∏ i, (μ₀.tilted ...) (s i)` に直接展開。`pi_eq` の `h` を「左辺 (tilted pi) box = ∏ tilted box」
     の形に揃え、左辺だけ `tilted_apply'` + Tonelli で潰す。**Tonelli は box 上 ∏-integrand の
     1 本だけで済む** (両側展開不要)。← **推奨**。
   - **経路 (b) — `withDensity` の `Measure.pi` 因子分解補題を独立に立てる**:
     `Measure.pi (fun i => (ν i).withDensity (gᵢ)) = (Measure.pi ν).withDensity (fun x => ∏ i, gᵢ (x i))`
     を汎用 PR-candidate として先に publish。これは Mathlib 本体に値する独立補題 (E 行 `Found 0`)。
     ただし汎用化コストが経路 (a) より重い (~+40 行)。

   経路 (a) の Tonelli ステップは `Measure.pi` の box 上 setLIntegral を coordinate ごとに
   `lintegral_indicator` + `pi_pi` で再帰展開、または `Fin n` の帰納で組む。
   **これが Phase 1 の唯一の重い箇所** (推定 60-100 行)。

4. **正規化定数の同一視** — `(∫ exp(lam·Y) ∂μ₀)^n` (左辺分母) と `∏ i, (per-coord 分母)` が一致することは
   `iIndepFun.cgf_sum` (`Basic.lean:393`) で exponent レベルでも裏取りできるが、Phase 1 では
   `Finset.prod_const` + product 積分因子化で純代数的に閉じる (確率独立性は不要、`pi` の積分因子化のみ)。

**Phase 1 で建てる補題群** (statement 明示):

```lean
-- 1-A: tilt density の積分解 (exp(∑) = ∏ exp)
lemma exp_sum_tilt_factor {n : ℕ} (Y : Ω₀ → ℝ) (lam : ℝ) (x : Fin n → Ω₀) :
    Real.exp (∑ i, lam * Y (x i)) = ∏ i, Real.exp (lam * Y (x i))

-- 1-B: product 上の正規化定数 = ∏ marginal 正規化定数
lemma integral_exp_sum_pi_eq_prod {n : ℕ} {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    ∫ x, Real.exp (∑ i, lam * Y (x i)) ∂(Measure.pi (fun _ : Fin n => μ₀))
      = (∫ ω, Real.exp (lam * Y ω) ∂μ₀) ^ n

-- 1-C: product Tonelli (box 上 ∏-integrand の lintegral 因子化) ★核
lemma setLIntegral_pi_prod_factor {n : ℕ} {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {g : Ω₀ → ℝ≥0∞} (hg : Measurable g) (s : Fin n → Set Ω₀) (hs : ∀ i, MeasurableSet (s i)) :
    ∫⁻ x in Set.pi Set.univ s, ∏ i, g (x i) ∂(Measure.pi (fun _ : Fin n => μ₀))
      = ∏ i, ∫⁻ ω in s i, g ω ∂μ₀

-- 1-D (本丸): 有限 tilt 因子分解 — これが最低保証 deliverable
lemma pi_tilted_sum_eq_pi_tilted {n : ℕ} {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    (Measure.pi (fun _ : Fin n => μ₀)).tilted (fun x => ∑ i, lam * Y (x i))
      = Measure.pi (fun _ : Fin n => μ₀.tilted (fun ω => lam * Y ω))
```

#### Phase 1 の証明武器在庫サマリ (本計画起草時 loogle 裏取り)

| 役割 | Mathlib lemma | file:line | 状態 |
|---|---|---|---|
| uniqueness (box 一致 ⇒ 測度一致) | `MeasureTheory.Measure.pi_eq` | `Constructions/Pi.lean:281` | ✅ |
| box 質量 (右辺展開) | `MeasureTheory.Measure.pi_pi` | `Constructions/Pi.lean:293` | ✅ |
| tilted box 質量 (左辺、measurable) | `ProbabilityTheory.tilted_apply'` | `Measure/Tilted.lean:101` | ✅ |
| tilted = withDensity | `ProbabilityTheory.tilted_eq_withDensity_nnreal` | `Measure/Tilted.lean:94` | ✅ |
| withDensity box apply | `MeasureTheory.withDensity_apply` | `Measure/WithDensity.lean:45` | ✅ |
| **product Tonelli (1-C)** | **不在** (`lintegral_pi` 直接形 `Found 0`) | — | ❌ 自前 |
| **`pi × withDensity` 因子分解 (経路 b)** | **不在** (`Found 0`) | — | ❌ 自前 |

### Chernoff 側 (`IsBayesErrorPerTiltLowerBound`) との共有可能性評価

在庫の気づき「Chernoff 側は pmf-level で `Measure.pi` 因子分解が無限積より楽な probe になりうる」を本計画で評価した結果:

- **Chernoff 側は `Measure.pi`/`infinitePi` を経由しない**。`ChernoffPerTiltDischarge.lean:136` の
  `IsBayesErrorPerTiltLowerBound (P₁ P₂ : α → ℝ) (lam : ℝ)` は pmf `P₁ P₂ : α → ℝ` 上の
  scalar `bayesErrorMinPmf P₁ P₂ n` (n-letter pmf 積の最小値) を直接扱い、`chernoffZSum P₁ P₂ lam ^ n`
  の形で n-letter 化が **pmf の `∏` (Finset.prod) として閉じている**。measure-theoretic な
  `Measure.pi` の box/cylinder/RN 微分は登場しない。
- 従って **Phase 1 の有限 `Measure.pi` tilt 因子分解補題を Chernoff 側がそのまま import する形にはならない**。
  共有できる core は「`exp(∑) = ∏ exp` + 正規化定数 `Z^n` の同一視」(1-A/1-B の代数核) **のみ**で、
  これは既に Chernoff 側で pmf の `Finset.prod` として閉じている (重複構築不要)。
- **判断**: 有限因子分解補題を Cramér/Chernoff 双方共有 core として 1 本にまとめるのは **不採用**。
  両者の n-letter object が異なる圏 (measure vs pmf) にあり、共有レイヤは scalar 代数核に留まる。
  本計画は **Cramér 側 (`IsMeasureInfinitePiTiltedEq`) に専念**し、Chernoff 側 `IsBayesErrorPerTiltLowerBound`
  の discharge は別 plan (`chernoff-converse-moonshot-plan.md` 系) に委ねる。Phase 1 補題は Cramér 専用。
  (この判断は §判断ログ #1 に記録。)

### 規模見積もり (Phase 別中央予測)

| Phase | 自作要素 | 想定行数 | proof-log |
|---|---|---|---|
| 0 | 在庫差分再確認 (起草時 loogle 済) | 0 (調査のみ) | no |
| 1 | 1-A exp_sum / 1-B 正規化 / **1-C Tonelli ★** / 1-D 本丸 + skeleton/imports | **~140-220** | yes |
| 2 | cylinder lift (両 ambient で `infinitePi_cylinder` + `infinitePi_eq_pi`) | ~50-90 | yes |
| 3 | change-of-measure + tilted LLN 合流 (`setLIntegral_rnDeriv` 経路) | ~70-120 | yes |
| 4 | `IsMeasureInfinitePiTiltedEq` discharge (C:=1/2 抽出) **or** residual 縮約 | ~40-80 | yes |
| V | verify + 親 plan 反映 | ~10-20 | no |
| **合計** | | **~310-530** | |

在庫の「Cramér 側だけで ~290-500 行」見積もりと整合。**Phase 1 単独 = ~140-220 行で PR 級 publish 価値**。

### 新ファイル / import / 検証

- **新ファイル**: `InformationTheory/Shannon/MeasurePiTiltedFactorization.lean`
  (有限 `Measure.pi` tilt 因子分解 = Phase 1。汎用 Mathlib-PR 候補として Cramér 文脈から切り離した独立 module)。
  - imports (pinpoint, `import Mathlib` 禁止):
    `Mathlib.MeasureTheory.Constructions.Pi`, `Mathlib.MeasureTheory.Measure.Tilted`,
    `Mathlib.Probability.Moments.Tilted` (`tilted_apply'` 等), `Mathlib.MeasureTheory.Measure.WithDensity`。
    Cramér 文脈 helper (`isProbabilityMeasure_tilted_of_bounded` 等) は Phase 2-3 着手時のみ追加。
- **Phase 2-4 配置判断**: Phase 1 を上記新 module に置いた上で、Phase 2-4 (cylinder lift + discharge) は
  - option (i): 同 module 末尾に追記 (Cramér 依存 import を追加)
  - option (ii, 推奨): `InformationTheory/Shannon/CramerLC2PhaseC.lean` 末尾に `infinitePi_tilted_discharge` を追記し
    Phase 1 module を import (述語定義と discharge が同一ファイルで近接)。
  Phase 2 着手時 (Phase 1 完遂後) に確定。default option (ii)。
- **`InformationTheory.lean`**: Phase 1 完遂時に `import InformationTheory.Shannon.MeasurePiTiltedFactorization` を追記。
- **検証ポイント**: 各 Phase 完了で `lake env lean <touched file>` silent (0 sorry / 0 warning)。
  upstream 編集後 dependents は `lake build InformationTheory.<module>` で olean refresh (CLAUDE.md)。

---

## Phase 0 — 在庫差分再確認 ✅

### スコープ

在庫 (`infinitepi-tilted-rn-discharge-mathlib-inventory.md`) の E 行 `Found 0` を Phase 1 着手直前に再裏取りし、Phase 1 の証明武器 (`pi_eq` / `pi_pi` / `tilted_apply'` / `withDensity_apply`) の正確な signature を確定する。

### 成果 (本計画起草時に完了)

- `Measure.pi × withDensity` / `Measure.pi × tilted` の collapse は **`Found 0`** を再確認 (loogle 起草時実行)。
- `Measure.pi_eq` (`Pi.lean:281`, `[∀ i, SigmaFinite (μ i)]` 前提), `Measure.pi_pi` (`Pi.lean:293`),
  `tilted_apply'` (`Tilted.lean:101`), `withDensity_apply` (`WithDensity.lean:45`),
  `tilted_eq_withDensity_nnreal` (`Tilted.lean:94`) の signature を §Approach の表に verbatim 反映済。
- **product Tonelli (`lintegral_pi` 直接形) は不在** を再確認 (1-C が唯一の自前核であると確定)。

### Done 条件 (満たし済)

- Phase 1 skeleton (1-A〜1-D) が書ける状態。**proof-log: no** (調査のみ)。

---

## Phase 1 — 有限 `Measure.pi` tilt 因子分解補題群 📋 (本丸・最優先・0-sorry 必達)

### スコープ

`MeasurePiTiltedFactorization.lean` に 1-A〜1-D (§Approach 参照) を skeleton-driven で建てる。
**1-D `pi_tilted_sum_eq_pi_tilted` が本計画の最低保証 deliverable**。

**proof-log**: yes (`proof-log-infinitepi-tilted-rn-phase1.md`)。

### Done 条件

- `InformationTheory/Shannon/MeasurePiTiltedFactorization.lean` 新規作成 + skeleton 全 `sorry` で type-check。
- 1-A〜1-D 全 0-sorry。`lake env lean InformationTheory/Shannon/MeasurePiTiltedFactorization.lean` silent。
- `InformationTheory.lean` に import 1 行追記。

### ステップ

- [ ] **1-0 skeleton + ファイル配置**: 1-A〜1-D を `:= by sorry` で並べた skeleton を Write、LSP 診断で type-check OK (sorry warning のみ)。imports は §新ファイル の pinpoint リスト。namespace `InformationTheory.Shannon.Cramer.Discharge` (既存 discharge 群と整合) または独立 `MeasureTheory` 拡張 namespace (PR 化を見据えるなら後者)。**Phase 1-0 で決定、default は既存 discharge namespace**。
- [ ] **1-1 Tonelli 経路確定 (a)/(b)**: §Approach の経路 (a) (推奨、box 上 ∏-integrand 1 本) か (b) (汎用 `pi × withDensity`) を実装着手で確定。経路 (a) で 1-C を `Fin n` の Tonelli 帰納 or `pi_pi` 再帰展開で組む方針を proof-log に記録。
- [ ] **1-2 1-A `exp_sum_tilt_factor`**: `Real.exp_sum` で `exp(∑) = ∏ exp`。~5-10 行。
- [ ] **1-3 1-B `integral_exp_sum_pi_eq_prod`**: product 上の積分因子化 + `Finset.prod_const`。bounded ⇒ integrable は既存 `integrable_exp_mul_of_bounded` (Cramér) 流用可だが本 module 独立性のため自前 5 行で済ませる選択肢も。~25-40 行。
- [ ] **1-4 1-C `setLIntegral_pi_prod_factor` (★核)**: box 上 ∏-integrand の lintegral 因子化。**Phase 1 の山場**。`Fin n` 帰納 (`Fin.cons` / `MeasurableEquiv.piFinSuccAbove` 経由) または `pi_pi` の lintegral 版を再構成。~60-100 行。
- [ ] **1-5 1-D `pi_tilted_sum_eq_pi_tilted` (本丸)**: `Measure.pi_eq` を `μ' := LHS.tilted ...` に適用、box 上で `tilted_apply'` (左) と `pi_pi` (右) を 1-A/1-B/1-C で結ぶ。~30-50 行。
- [ ] **1-6 verify**: `lake env lean` silent 確認、`InformationTheory.lean` import 追記。

### 工数感

~140-220 行。0.75-1.25 セッション。**本セッションのゲート**。proof-log `yes`。

### 失敗時 fallback

- **1-4 Tonelli が `Fin n` 帰納で詰まる**: 経路 (a) → (b) に切替 (`pi × withDensity` 汎用補題を `Measure.pi_eq` で直接立てて tilt は corollary 化)、または `MeasureTheory.lintegral_eq_lmarginal_univ` (`Marginal.lean`, Phase 0 loogle で hit) 経由で marginal 積分の逐次化を使う。+30-40 行。
- **1-4 が 2 セッション詰まり**: §撤退ライン W-1 発動 (Tonelli 補題を `n=1`/`n=2` の特例 + box の自前帰納に縮退、または proof-pivot-advisor 相談)。

---

## Phase 2 — cylinder lift 📋

### スコープ

width-n event `{ω : ℕ → Ω₀ | a·n ≤ ∑_{i<n} Y(ωᵢ)}` を range n の cylinder と同定し、
`infinitePi_cylinder` (`ProductMeasure.lean:514`) / `infinitePi_eq_pi` (`:509`) で **tilted ambient と un-tilted ambient の両側で** `infinitePi` 質量を `Measure.pi (Fin n)` 質量に落とす。Phase 1 の有限因子分解を cylinder 上で起動可能にする。

**proof-log**: yes。

### Done 条件

- `event_eq_cylinder` (width-n event が `cylinder (Finset.range n) S` 形であることの同定)。
- `infinitePi_event_eq_pi` (両 ambient で `(infinitePi ...).real event = (Measure.pi (Fin n) ...).real S`)。
- beta-redex 迂回 (在庫の罠): `isProbabilityMeasure_infinitePi_tilted_of_bounded` (既存 `CramerLC2DischargeExt`) を全所で `haveI` 先置き。

### ステップ

- [ ] **2-1 event ↔ cylinder 同定**: `Finset.range n` のインデックスと `Fin n` の対応 (`Finset.range n ≃ Fin n`)、event の `∑ i ∈ Finset.range n` を `Fin n` の `∑ i` に書き換え。cylinder の `cylinder s S` 定義に合わせて `S` を構成。~30-50 行。
- [ ] **2-2 両 ambient で `infinitePi` → `Measure.pi (Fin n)`**: `infinitePi_cylinder` + `infinitePi_eq_pi`。beta-redex haveI 先置き。~20-40 行。
- [ ] **2-3 verify**: `lake env lean` silent。

### 工数感

~50-90 行。0.5-0.75 セッション。proof-log `yes`。

### 失敗時 fallback

- **2-1 `Finset.range n ≃ Fin n` の index 書き換えが煩雑**: `infinitePi_pi` (`:402`, box 質量 = `∏`) 経路に切替、cylinder を明示 box に展開。または event を半空間 indicator として `lintegral_restrict_infinitePi` (`:576`) で直接落とす。

---

## Phase 3 — change-of-measure + 既存 tilted LLN 合流 📋

### スコープ

Phase 1 (有限因子分解) + Phase 2 (cylinder lift) を結合し、un-tilted pi 上の event 質量に下界
`exp(-n(λa-Λ(λ)+λε)) · (tilted pi 上の絞った event 質量)` を貼る。絞った event
`{|S̄_n - a| < ε}` の tilted 質量 → 1 を `CramerLC2DischargeExt.tilted_lln_in_probability_real` で供給。

**proof-log**: yes。

### Done 条件

- `change_of_measure_lower_bound` (un-tilted pi event ≥ `exp(...)` · tilted pi event)。
  RN 微分 = `exp(lam·∑Y(ωᵢ) − n·Λ(lam))` を Phase 1 の因子分解 + `setLIntegral_rnDeriv` (`RadonNikodym.lean:333`) または `tilted_apply'` 直接で出す。
- `tilted_event_eventually_half` (絞った event の tilted 質量が `∀ᶠ n, ≥ 1/2`、既存 LLN から)。

### ステップ

- [ ] **3-1 RN 微分 = exp 形の確立**: Phase 1 `pi_tilted_sum_eq_pi_tilted` から `(pi μ₀).tilted (∑) = pi (μ₀.tilted)` を使い、`tilted_apply'` で un-tilted pi event 質量を tilted pi 上の `∫⁻ exp(λ·∑Y − n·Λ)` に書き換え。`cgf Y μ₀ lam` と正規化定数 `Z^n` の同一視 (`iIndepFun.cgf_sum` or 1-B)。~40-70 行。
- [ ] **3-2 LLN 合流**: 絞った event `{|S̄_n - a| < ε}` ⊆ `{a·n ≤ ∑Y}` (containment、`lam ≥ 0` の符号注意) を確立、tilted 質量 → 1 を `tilted_lln_in_probability_real` で eventually `≥ 1/2` に。~30-50 行。
- [ ] **3-3 verify**: `lake env lean` silent。

### 工数感

~70-120 行。0.75-1 セッション。proof-log `yes`。

### 失敗時 fallback

- **3-1 で `infinitePi (fun _ => μ₀.tilted)` (tilted ambient, 既存 LLN 側) と `Measure.pi (Fin n) (μ₀.tilted)` (Phase 1 側) の cylinder 整合が崩れる**: Phase 2 の `infinitePi_event_eq_pi` を tilted ambient 側にも適用して両者を `Fin n` pi で揃える (Phase 2 で両 ambient 対応済なら無料)。
- **3-2 containment の符号で詰まる**: `a·(1-ε') ≤ S̄_n` の ε-neighborhood を明示し `lam·(a+ε)` の余裕で吸収 (親 plan `cramer-lc2-discharge` Phase C-2 の C:=1/2 構成と同型)。

---

## Phase 4 — `IsMeasureInfinitePiTiltedEq` discharge or residual 縮約 📋

### スコープ

Phase 1-3 を合成し `IsMeasureInfinitePiTiltedEq μ₀ Y lam` を `∀ a ε, ∃ C:=1/2, ∀ᶠ n` の形で 0-sorry 充足。
`cramer_lower_phaseC_partial_discharge` 系の `h_pred` を内部供給して `h_pred` 引数なしの完全 wrapper を publish。

**閉じない場合は sorry を残さず residual predicate へ縮約** (撤退ライン W-3、§撤退ライン)。

**proof-log**: yes。

### Done 条件 (full discharge シナリオ)

- `infinitePi_tilted_eq_discharge : IsMeasureInfinitePiTiltedEq μ₀ Y lam` (bounded measurable Y, `0 ≤ lam`)。
- `cramer_lower_full_discharge` 等 = `cramer_lower_phaseC_partial_discharge` の `h_pred` を内部供給した wrapper。

### ステップ

- [ ] **4-1 述語の `∀ a ε, ∃ C, ∀ᶠ n` 形に Phase 3 を流し込む**: `C := 1/2`、Phase 3 の下界 + eventually `≥ 1/2` で `1/2 · exp(-n(λa-Λ+λε)) ≤ (infinitePi μ₀).real event` を出す。~30-50 行。
- [ ] **4-2 完全 wrapper publish**: `cramer_lower_phaseC_partial_discharge` 系を `h_pred` 内部供給で再 publish。~15-30 行。
- [ ] **4-3 verify + 親 plan 反映**: §Phase V。

### 工数感

~40-80 行。0.5-0.75 セッション。proof-log `yes`。

### 失敗時 fallback (residual 縮約、sorry 禁止)

§撤退ライン W-3 参照。`IsMeasureInfinitePiTiltedEq` を Phase 1-3 で済んだ部分を吸収した
**strictly smaller residual predicate** へ縮約する (具体形は §撤退ライン)。

---

## Phase V — verify + 親 plan 状態反映 📋

### スコープ

- `lake env lean` 全 touched file clean (0 sorry / 0 warning)。
- `CramerLC2PhaseC.lean` の述語コメントに「有限因子分解は本 module で discharge 済 / 残りは X」を追記 (Phase 4 シナリオに応じて)。
- 親 plan (`cramer-lc2-discharge-moonshot-plan.md` / `cramer-lc2-ext-moonshot-plan.md`) の Phase C 状態絵文字を更新、判断ログ append。
- 本 plan の進捗ブロック更新 + 判断ログ append。

**proof-log**: no。工数 ~10-20 行 / 編集のみ。

---

## 撤退ライン

### Scope 縮小ライン (sorry 禁止、predicate 化で抜く)

- **W-1 — Phase 1-4 Tonelli が割れない**: 経路 (a) → (b) 切替、それでも 2 セッション詰まりなら
  Tonelli を `Marginal.lean` の `lmarginal` 逐次積分経由に切替。最低保証 (1-D) が割れない場合のみ
  **本計画全体 PIVOT** (1-D は本計画の存在意義そのもの)。
  - **proof-pivot-advisor 相談トリガ**: 1-4 (Tonelli) で **3 ターン**詰まったら相談。

- **W-2 — Phase 2/3 cylinder lift or change-of-measure が割れない**: Phase 1 (有限因子分解) のみを
  独立 publish (PR 級 deliverable として確定)。`IsMeasureInfinitePiTiltedEq` は触らず、`CramerLC2PhaseC.lean`
  の述語は現状維持。本計画は Phase 1 + V で close (最低保証達成)。proof-log に Phase 2/3 の詰まり記録。
  - **proof-pivot-advisor 相談トリガ**: Phase 3-1 (RN 微分形確立) で **4 ターン**詰まったら相談。

- **W-3 — Phase 4 full discharge が割れない (residual 縮約、sorry 禁止)**:
  Phase 1-3 で確立した有限因子分解 + cylinder lift + change-of-measure を吸収した
  **strictly smaller residual predicate** を `CramerLC2PhaseC.lean` の `IsMeasureInfinitePiTiltedEq` の
  代わりに導入する。具体形:
  ```lean
  -- residual: Phase 1-3 を吸収後、残るのは「絞った event の tilted 質量が eventually ≥ 1/2」
  -- = 既存 tilted_lln_in_probability_real から従うべきだが Phase 3-2 の containment が
  --   未完の場合に切り出す残差。
  def IsTiltedEventEventuallyLarge (μ₀ : Measure Ω₀) (Y : Ω₀ → ℝ) (lam : ℝ) : Prop :=
    ∀ a ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / 2 ≤ (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).real
          {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)}
  -- そして `IsTiltedEventEventuallyLarge → IsMeasureInfinitePiTiltedEq` を 0-sorry で publish。
  -- = 元の述語より strictly smaller (RN 微分・因子分解部分は本計画で discharge 済、
  --   tilted-side LLN containment のみ残差)。
  ```
  この縮約版 wrapper (`isMeasureInfinitePiTiltedEq_of_tiltedEventLarge`) を 0-sorry で publish し、
  残差 `IsTiltedEventEventuallyLarge` は次セッションで `tilted_lln_in_probability_real` から閉じる。
  **sorry は一切残さない**。

### 自作 plumbing 肥大ライン

- **W-DP1 — Phase 1 namespace を PR 化向けに `MeasureTheory` 拡張に置くと既存 discharge と齟齬**:
  既存 discharge namespace (`InformationTheory.Shannon.Cramer.Discharge`) に置く (PR 化は後日 extract)。
- **W-DP2 — beta-redex 罠 (在庫の罠) が Phase 2/3 で再発**: 全所で
  `isProbabilityMeasure_infinitePi_tilted_of_bounded` を `haveI` 先置き (`CramerLC2DischargeExt` 既存パターン踏襲)。

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| **product Tonelli (1-C) の `Fin n` 帰納が重い** | **高** (在庫 `Found 0`、自前核) | **高** (Phase 1 +40-60 行) | 経路 (a)/(b) 切替、`lmarginal` 経由、W-1 |
| `Measure.pi_eq` の `[SigmaFinite]` 前提が prob から auto-derive されない | 低 | 低 (`haveI` 1 行) | 有限測度 ⇒ SigmaFinite instance 確認 |
| beta-redex 罠 (`infinitePi (fun _ => tilted)` の instance) | **高** (在庫実証済) | 中 (haveI 先置き) | `isProbabilityMeasure_infinitePi_tilted_of_bounded` 全所 haveI |
| Phase 2 の `Finset.range n ≃ Fin n` index 書き換えが煩雑 | 中 | 中 (Phase 2 +20-30 行) | `infinitePi_pi` box 経路、半空間 indicator 直接 |
| Phase 3 change-of-measure で tilted/un-tilted ambient の cylinder 整合崩れ | 中-高 | 中-高 (W-2) | Phase 2 で両 ambient 対応、`Fin n` pi で揃える |
| Phase 3-2 containment の符号 (`lam ≥ 0`) で詰まる | 中 | 中 | 親 plan Phase C-2 の ε-neighborhood 構成踏襲 |
| 本セッションで Phase 1 完遂不能 | 中 | 中 (最低保証未達、W-1) | Phase 1 単独でゲート設計、3 ターン詰まりで proof-pivot 相談 |
| full discharge がセッション内不能 | **高** (確定済) | 中 (W-3 residual 縮約) | Phase 4 residual predicate 化、sorry 禁止 |

---

## 危険箇所（実装着手時に注意）

CLAUDE.md "Mathlib-shape-driven Definitions" + "Subagent Inventory" 規約に従い、着手時に特に注意:

1. **Phase 1 の因子分解は `Measure.pi_eq` の conclusion form に乗せる** (textbook 形を直書きしない)。
   左辺 `(pi μ₀).tilted (∑)` の box 質量を `tilted_apply'`、右辺 `pi (μ₀.tilted)` の box 質量を `pi_pi` で
   出し、両者を 1-C Tonelli で結ぶ。**`tilted` を coord-wise map で書く誘惑は破綻** (在庫 `infinitePi_map_pi`
   の注: tilt は coord-wise map ではなく withDensity)。

2. **`tilted_apply'` の `Integrable (exp ∘ f)` 前提** (n=1 版 `tilted_mul_apply_cgf` も同様):
   bounded Y で自動だが、product `Measure.pi` 上の `exp(∑ lam·Y(x i))` の integrability は
   `∏ exp` の product integrability に分解 (1-B で正規化定数を出す際に併せて確立)。

3. **`Measure.pi_eq` の `[∀ i, SigmaFinite (μ i)]`**: `μ i := μ₀.tilted (lam·Y·)` が SigmaFinite であること。
   `isProbabilityMeasure_tilted_of_bounded` (既存) で IsProbabilityMeasure ⇒ SigmaFinite auto。

4. **beta-redex 罠 (在庫の罠、実証済)**: `Measure.infinitePi (fun _ => μ₀.tilted ...)` の instance synthesis が
   `(fun _ => ...) i` を β-簡約しない。Phase 2/3 の tilted ambient を扱う全所で
   `isProbabilityMeasure_infinitePi_tilted_of_bounded` を `haveI` 先置き (`CramerLC2DischargeExt` パターン)。

5. **`cgf Y μ₀ lam` と正規化定数 `(∫ exp(lam·Y))^n` の同一視**: `cgf = log mgf = log ∫ exp`。
   `n·Λ(lam)` の exponent は `iIndepFun.cgf_sum` で裏取りできるが、Phase 1 では純代数 (1-B の `Z^n`) で閉じる。

6. **Chernoff 側を巻き込まない** (§Approach 評価): Phase 1 補題は Cramér 専用。Chernoff 側
   `IsBayesErrorPerTiltLowerBound` の pmf-level n-letter 化と本計画の measure-level 因子分解は別圏。

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(2026-05-20) 起草時判断: Chernoff 側との core 共有は不採用、Cramér 専念**:
   在庫の気づき「Chernoff 側 pmf-level が `Measure.pi` 因子分解の楽な probe になりうる」を評価。
   `ChernoffPerTiltDischarge.lean:136` の `IsBayesErrorPerTiltLowerBound (P₁ P₂ : α → ℝ)` は
   pmf 上の scalar `bayesErrorMinPmf` / `chernoffZSum^n` を扱い、measure-theoretic な
   `Measure.pi`/`infinitePi`/cylinder/RN 微分を **一切経由しない**。n-letter 化は pmf の
   `Finset.prod` として既に閉じている。よって Phase 1 の有限 `Measure.pi` tilt 因子分解補題を
   Chernoff 側が import する形にはならず、共有 core は scalar 代数核 (`exp(∑)=∏exp` + `Z^n`) のみで
   これは Chernoff 側で既存。**判断: 有限因子分解補題は Cramér 専用 (Phase 1 module は Cramér 文脈)**、
   Chernoff discharge は別 plan に委ねる。

2. **(2026-05-20) 起草時判断: Phase 1 を独立 module `MeasurePiTiltedFactorization.lean` に切り出し**:
   有限 `Measure.pi` tilt 因子分解は汎用 Mathlib-PR 候補 (E 行 `Found 0`)。Cramér 文脈 import を
   持たない独立 module に置くことで (a) PR 化時の extract が容易、(b) 最低保証 deliverable が
   Cramér 依存なしで単独 verify 可能、(c) Phase 2-4 (Cramér 依存) を別ファイル/末尾に分離。
   default namespace は既存 discharge (`InformationTheory.Shannon.Cramer.Discharge`)、PR 化は後日。
