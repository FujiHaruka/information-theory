# RD achievability: 完全一般 source 版 (full-support 前提の除去) サブ計画

> **Parent**: [`rate-distortion-achievability-unconditional-plan.md`](rate-distortion-achievability-unconditional-plan.md) /
> [`textbook-roadmap.md`](../textbook-roadmap.md) §Ch.10 frontier「壁ではない frontier」
>
> **Status**: **CLOSED ✅ (2026-07-13)** — `rate_distortion_achievability_operational_general`
> (`@[entry_point]`, `AchievabilityGeneralSource.lean:410`) genuine proof-done / sorryAx-free /
> 独立 honesty 監査 `@audit:ok` (`a4d6763c` + audit commit)。G0–G4 + Wrapper 全 proof done。
> gateway G1 (restrict/pad 全単射 + 3 統計量保存) は finite-sum algebra で一発通過し approach 確定。
> G4 の pushforward/marginal は `Measure.pi_map_pi` + `measurePreserving_eval` + `integral_map` で
> 賄え、予測した自作 `Measure.pi` null 積補題は**不要**だった (facts ledger 参照)。
> 新 load-bearing hyp ゼロ (`hP_supp` を除いただけ、監査確認)。

## Context

現行 headline `rate_distortion_achievability_operational`
(`InformationTheory/Shannon/RateDistortion/AchievabilityUnconditional.lean:568`) は
**full-support 前提** `hP_supp : ∀ a, 0 < P_X a` を持つ。これは marginal 保存摂動
`rdPerturb` が joint を strict-positive に着地させる必要 (strong track の `qZ_min > 0`)
に由来する regularity precondition (load-bearing でない、独立監査 PASS 済)。

残る唯一の Ch.10 scope-out = **この前提を落とした任意 source 版**。roadmap 判定は
「真の壁ではない、regularity 緩和」。退化境界 verify (source = Dirac `(1,0)`) で
統計量が台のみに依存 → 台上で full-support 版が走り非台シンボルは a.s. 出現しない、
で成立確認済 = **真の定理**、量の壁クラス、Mathlib gap 想定なし。

## Approach

**台 subtype への制限 → full-support 版適用 → code を全 alphabet に lift**。

- `α' := {a // 0 < P_X a}` — subtype。instance は全て導出可:
  `Fintype`/`DecidableEq`/`MeasurableSpace`/`MeasurableSingletonClass` は subtype instance、
  `Nonempty` は `∑ P_X = 1 > 0` から `∃ a, 0 < P_X a`。
- `P_X' : α' → ℝ := fun a ↦ P_X a.1` — full-support (`0 < P_X a.1` は subtype 定義)、stdSimplex。
- `d' : DistortionFn α' β := fun a b ↦ d a.1 b`。
- **joint の zero-pad / restrict 対応**: `RDConstraint P_X d D` の joint `q` は
  `marginalFst q = P_X` かつ `q ≥ 0` (stdSimplex) ゆえ `P_X a = 0 ⟹ q(a,b) = 0`
  (nonneg 和がゼロ) = 台外の行はゼロ。よって α×β 上の joint ↔ α'×β 上の joint が全単射
  (`restrict`/`pad`)。この対応で `mutualInfoPmf`/`expectedDistortionPmf`/`marginalFst`
  が保存 (`negMulLog 0 = 0`、`0·d = 0`、台外行の marginal もゼロ)。
- これで `R(D)` が α と α' で一致 → 前提を α' に移送 → full-support 版適用 →
  `c' : LossyCode M n α' β` を得る → retraction `r : α → α'` (台上恒等、台外は default `a₀`)
  で `c : LossyCode M n α β` に lift → 期待歪みが `Measure.pi (pmfToMeasure P_X)` の下で
  一致 (台外座標を含む列は測度ゼロ、`integral_congr_ae`)。

target signature (full-support 版から `hP_supp` を除いただけ):

```lean
theorem rate_distortion_achievability_operational_general
    (P_X : α → ℝ) (hP_pmf : P_X ∈ stdSimplex ℝ α)
    (d : DistortionFn α β) {D : ℝ}
    (h_ne : (RDConstraint P_X d D).Nonempty)
    {R : ℝ} (hR : rateDistortionFunctionPmf P_X d D < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (_hM_ub : (M : ℝ) ≤ Real.exp ((n : ℝ) * R) + 1)
        (c : LossyCode M n α β),
        c.expectedBlockDistortion (pmfToMeasure (α := α) P_X) d ≤ D + ε
```

**File**: 新規 `InformationTheory/Shannon/RateDistortion/AchievabilityGeneralSource.lean`
(imports `AchievabilityUnconditional`)。`InformationTheory.lean` に import 登録。

## Pieces

- **G0 (support-zero lemma)**: `q ∈ stdSimplex ∧ marginalFst q = P_X ∧ P_X a = 0 → ∀ b, q (a,b) = 0`
  (nonneg 有限和ゼロ)。台外行ゼロの基盤。
- **G1 (restrict/pad 対応 + 統計量保存)** 🎯 **gateway**: `restrict q : α'×β → ℝ`,
  `pad q' : α×β → ℝ` を定義し、`RDConstraint P_X d D` 上で `pad (restrict q) = q` (G0)、
  `mutualInfoPmf (pad q') = mutualInfoPmf q'` (α' 版)、`expectedDistortionPmf d (pad q') =
  expectedDistortionPmf d' q'`、`marginalFst (pad q') = pad-marginal` を証明。
  **ここが機構検証点** — 全単射 + 3 統計量保存が finite-sum algebra (`negMulLog 0 = 0`) で
  閉じるかを最初に確認。閉じれば残りは移送 + measure plumbing。
- **G2 (R(D) 不変)**: `rateDistortionFunctionPmf P_X d D = rateDistortionFunctionPmf P_X' d' D`。
  `mutualInfoPmf '' RDConstraint P_X d D = mutualInfoPmf '' RDConstraint P_X' d' D` (G1 の全単射)
  → sInf 一致。
- **G3 (前提移送)**: `(RDConstraint P_X' d' D).Nonempty` (G1) / `R(D') < R` (G2)。
- **G4 (code lift + 期待歪み一致)**: full-support 版を α' に適用 → `c'`。
  retraction `r : α → α'` (`fun a ↦ if h : 0 < P_X a then ⟨a,h⟩ else a₀`) で
  `c.encoder x := c'.encoder (r ∘ x)`, `c.decoder := c'.decoder`。
  `pmfToMeasure P_X {a | ¬ 0 < P_X a} = 0` + `Measure.pi` の full-measure 積 →
  「全座標が台」集合が full measure → `blockDistortion d n x (…) = blockDistortion d' n (r∘x) (…)`
  が a.e. → `integral_congr_ae` で `expectedBlockDistortion` 一致。
- **Wrapper**: G2/G3 で full-support 版を呼び、G4 で歪みを引き戻す。

## 実装順 (gateway-atom-first)

1. **M0 在庫**: subtype instance の導出可否 (`Subtype.fintype` 等) と、
   `Measure.pi` の full-measure 積補題・`pmfToMeasure` の台補集合ゼロを loogle 確認。proof-log: no。
2. **G0 → G1 (gateway)** を単独で閉じる。G1 の 3 統計量保存が閉じれば approach 確定。proof-log: yes。
3. **G2 → G3**。
4. **G4** (measure a.e. 引き戻し)。
5. **Wrapper**。
6. **独立 honesty audit**: 新 sorry があれば `@residual` 分類、無ければ 0-sorry proof done 確認
   (subtype instance が hidden hypothesis を持ち込んでいないか、`a₀` default が結論を汚さないか)。

## 想定リスク (壁誤認しそうな点)

1. **G1 の全単射**: `pad ∘ restrict = id` on RDConstraint は G0 依存。台外行を落として復元、
   finite。詰まっても壁でなく plumbing。
2. **G4 の `Measure.pi` full-measure**: `Measure.pi_pi` / `MeasureTheory.ae_eq` の積。
   Mathlib に `Measure.pi` の null-set 積補題があるはず (M0 で確認)。無ければ有限積の
   `measure_iInter`/finite で self-build、壁ではない。
3. **retraction の可測性**: `r : α → α'` は α 有限 (MeasurableSingletonClass) ゆえ
   `measurable_of_countable`/`measurable_of_finite` で自動。encoder は `Fin n → α → Fin M`、
   LossyCode は可測性を要求しない (structure が encoder/decoder のみ) ので lift は関数合成のみ。
4. **`R(D')` 型不一致**: `rateDistortionFunctionPmf` は同型 (`α'` 版)。G2 で verbatim `=` を
   `linarith`/`rw` で確認。

## 判断ログ

active な判断のみ。決着済は削除 (git 履歴)。予算 ≤ 600 行 / ≤ 10 entry。

1. **台 subtype 制限を採用** (起草時): 摂動作り替えでは joint strict-positivity を作れない
   (marginal 保存が台外行をゼロ強制)。full-support 版を unchanged で再利用するには台に落とすのが
   最小変更。alphabet 型変更のコストは G1 全単射 + G4 a.e. に局在。
