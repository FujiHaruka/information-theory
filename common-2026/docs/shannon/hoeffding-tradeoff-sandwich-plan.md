# Hoeffding tradeoff sandwich discharge サブ計画 🌙

> **Parent**: [`hoeffding-tradeoff-moonshot-plan.md`](hoeffding-tradeoff-moonshot-plan.md) §Phase C/D (L-H4 で defer された achievability `h_liminf` + converse `h_limsup`)
> **在庫**: [`hoeffding-sandwich-discharge-inventory.md`](hoeffding-sandwich-discharge-inventory.md)

<!--
記法は moonshot-plan-template と同じ:
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)`
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 削除/廃止 Phase は ~~取り消し線~~ で残す（過去参照のため）
- 判断ログは append-only
-->

## 進捗

> 🛑 **BLOCKED — DEF-FLAW 発見 (2026-05-21)**: headline `rate → hoeffdingE2 P₁ P₂ alpha` は
> 現 operational 定義 `steinTypeII_at_level_pmf` (定数 Type-I level `alpha`) では **数学的に偽**。
> tradeoff 曲線 `E₂(alpha)` は **指数 level** `α_n = exp(-nr)` 領域でのみ極限になる。固定 α では
> Stein により `rate → D(P₁‖P₂) = E₂(0)`、α>0 では `E₂(alpha) < E₂(0)` なので `rate ≠ E₂(alpha)`。
> α=0 でも反例 (`steinTypeII ≡ 1` ⟹ `rate ≡ 0 ≠ D > 0`)。詳細は判断ログ #4 + コード docstring
> (`HoeffdingSandwichDischarge.lean:139-185`)。**full discharge には operational 量の指数 level
> 再定義が必須** (= 新サブ計画 `hoeffding-exponent-level-redef-plan.md` 待ち、本計画の Phase 3/4 は無効化)。

- [x] Phase 0 — signature 再確認 + skeleton 配置 ✅
- [x] Phase 1 — `hoeffdingE2 = klDivPmf Qstar P₂` の 3-case 確立 (constructive full-support Qstar) ✅ (`exists_hoeffding_minimizer_full_support`, genuine 0-sorry, L-H4 完全回避)
- [~] Phase 2 — converse `h_limsup ≤ E2` 🔄 boundary case (`klDivPmf P₂ P₁ ≤ alpha`、E2=0 collapse) のみ genuine (`hoeffding_tradeoff_achievability_at_boundary`)。一般 α は DEF-FLAW で偽のため不可。
- [x] ~~Phase 3 — achievability via Sanov lower + Type-I AEP~~ 🔄 **無効化** (DEF-FLAW: 定数 α では Sanov lower が tradeoff 曲線に接続しない)
- [x] ~~Phase 4 — 3-case 統合して headline hypothesis-free~~ 🔄 **無効化** (headline が偽)。honest wrapper `hoeffding_tradeoff_of_asymptotics` (変分 2 不等式を明示仮説、`:= True`/sorry なし) で着地。
- [x] Phase V — clean check + `Common2026.lean` 編入 ✅ (`HoeffdingSandwichDischarge.lean` 202 行, 0 sorry)

proof-log: 不要になった (Phase 3 無効化)。代わりに DEF-FLAW を判断ログ #4 に記録。

## ゴール / Approach

### ゴール

親 plan の headline `hoeffding_tradeoff_with_hypothesis` (`HoeffdingTradeoff.lean:296`) /
slim wrapper `hoeffding_tradeoff_sandwich` (`HoeffdingSandwich.lean:290`) に残る **2 本の変分仮定**
`h_liminf` (achievability) / `h_limsup` (converse) を discharge し、**hypothesis-free** な

```lean
theorem hoeffding_tradeoff
    (P₁ P₂ : α → ℝ) (hP₁_pos hP₂_pos : ∀ a, 0 < ·) (hP₁_sum hP₂_sum : ∑ = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < 1) :
    Tendsto (fun n => -((1:ℝ)/n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha))
      atTop (𝓝 (hoeffdingE2 P₁ P₂ alpha))
```

を publish する。境界条件は `alpha < 1` のみ (sandwich wrapper の要求と一致;
`alpha < klDivPmf P₁ P₂` は **不要** — boundary 域も 3-case で吸収する)。

### Approach (中核設計: abstract L-H4 を回避する constructive 3-case 分割)

親 plan は両側 (achievability/converse) が `csiszar_pythagoras_inequality` / `sanov_ldp_lower_bound_pointwise`
の `*_pos` (full-support) 引数を要求し、その供給を **abstract L-H4 補題
`hoeffdingE2_minimizer_full_support`** (log-singularity gradient 引数, 30-50 行) に依存していた。
本 plan は **この abstract 補題を回避する**。

代わりに **`alpha` を `klDivPmf P₂ P₁` を境に 3-case 分割**し、各ケースで `Qstar` を
**explicit に構成** すれば full-support は構成的に自明になる。**3 case とも constructive な
machinery が既に in-file で 0-sorry 完成済**である (在庫 §D + 直接確認済):

| case | 域 | Qstar | full-support の根拠 | `hoeffdingE2 = klDivPmf Qstar P₂` の根拠 |
|---|---|---|---|---|
| **(a) α = 0** | `alpha = 0` | `P₁` (boundary) | `hP₁_pos` | `hoeffdingE2_minimizer_at_boundary_alpha_zero` (`HoeffdingSandwichBody.lean:168`) + K = {P₁} singleton |
| **(b) 内部** | `0 < α ≤ klDivPmf P₂ P₁` | `hoeffdingTilt P₁ P₂ lam`, `lam ∈ Ioc 0 1` | `hoeffdingTilt_pos` (`HoeffdingInteriorGradientBody.lean:112`) | `exists_isHoeffdingLagrangeHyp_interior` (`HoeffdingMinimizerAttainment.lean:266`) の `.realises` |
| **(c) boundary** | `klDivPmf P₂ P₁ ≤ α` | `P₂` (boundary) | `hP₂_pos` | `hoeffdingE2_minimizer_at_boundary_alpha_ge_kl` (`HoeffdingSandwichBody.lean:228`) |

各 case は `∃ Qstar ∈ K, hoeffdingE2 = klDivPmf Qstar P₂ ∧ (∀ a, 0 < Qstar a)` を供給する
(case (b) は `IsHoeffdingInteriorMinimizer` 経由、`isHoeffdingInteriorMinimizer_of_constraint_eq`
`HoeffdingMinimizerAttainment.lean:296` でも取り出せる)。

**統一インターフェース**: Phase 1 でこの 3-case を 1 本の補題

```lean
lemma exists_hoeffding_minimizer_full_support
    (P₁ P₂ : α → ℝ) (hP₁_pos hP₂_pos) (hP₁_sum hP₂_sum)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) :
    ∃ Qstar ∈ hoeffdingConstraintSet P₁ alpha,
      hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂ ∧ (∀ a, 0 < Qstar a)
```

に集約する (`rcases` で 3-case 分岐, 各 case 既存補題で close, ~25-40 行)。
これが **L-H4 (`hoeffdingE2_minimizer_full_support`) の構成的代替**になり、以降の Phase 2/3 は
この `Qstar` をそのまま受け取って Sanov/Stein を起動する。

その上で 2 漸近不等式を組む (在庫 §A/§C):

- **converse `h_limsup`** (Phase 2, reuse ~80%): Phase 1 の `Qstar` (full-support) を
  `pmfToMeasure` で Measure 化し、`stein_strong_lemma` (`StrongStein.lean:498`,
  strict Tendsto, `1-ε` 因子なし) を `P := Qstar_meas, Q := P₂_meas` で起動。
  `(klDiv Qstar_meas P₂_meas).toReal` を 3 段橋
  (`klDivPmf → klDivSumForm_ofVec → klDivSumForm(Measure) → klDiv.toReal`,
  在庫 §B) で `hoeffdingE2 = klDivPmf Qstar P₂` に一致させる。任意 test の `Q ∈ K` を
  `csiszar_pythagoras_at_interior` (`HoeffdingInteriorBody.lean:245`) / 境界 case では
  E2 = 0 collapse で支配。`.eventually_le` で `limsup ≤ E2`。
- **achievability `h_liminf`** (Phase 3, 高リスク): `sanov_ldp_lower_bound_pointwise`
  (`SanovLDPEquality.lean:1071`, `-klDivSumForm_ofVec Qstar P₂ ≤ liminf (1/n)log P₂^n(⋃ T_c)`)
  を `Q := P₂_meas, P := Qstar` で起動。acceptance region `E_n := {c | (c/n) ∈ K}` の Finset 化
  (classical decidable) + `roundedTypeIndex Qstar n ∈ E_n` の eventually 性 (KL 連続 +
  `roundedTypeIndex_tendsto_vec`)。**最大の novel piece**: Type-I 制御 AEP
  `P₁^n(⋃ T_c) ≥ 1-α` (~30-50 行) — 既存 `typicalSet_prob_*` は entropy-band で set が違い直接流用不可。
  `steinTypeII ≤ P₂^n(⋃ T_c)` で liminf rate を下から `E2` で抑える。

### Approach 図

```
Phase 0 : signature 再確認 + skeleton 4 lemma を := by sorry で配置        ← 0.25 セッション (~60 行)
Phase 1 : exists_hoeffding_minimizer_full_support (3-case)                ← 0.5 セッション (25-40 行)
           ←─── 既存 constructive machinery 100% reuse, L-H4 回避 ───→
Phase 2 : converse h_limsup (Stein strong + Pythagoras)                   ← 1.0 セッション (80-120 行)
           ←─── reuse ~80%, 先に着手 ───→
Phase 3 : achievability h_liminf (Sanov lower + Type-I AEP)               ← 1.5 セッション (120-180 行)
           ←─── 撤退ライン L-H4-FB (boundary-only に縮退) ───→
Phase 4 : headline hypothesis-free (sandwich wrapper に流し込み)          ← 0.25 セッション (10-20 行)
Phase V : clean check + Common2026.lean 編入 (オーケストレータ)            ← 5 分
```

### ファイル構成

新規 `Common2026/Shannon/HoeffdingSandwichDischarge.lean` を想定 (在庫 §着手 skeleton 準拠)。
既存 `HoeffdingSandwichBody.lean` 拡張でも可だが、(1) Sanov/Stein/AEP の重い import が
sandwich body に波及するのを避ける、(2) Phase 単位で分離検証したい、の 2 理由で **新規ファイル推奨**。
import は在庫 §着手 skeleton の 9 本 + 構成的 machinery (`HoeffdingMinimizerAttainment`,
`HoeffdingInteriorBody`, `HoeffdingInteriorGradientBody`, `HoeffdingLagrangeIVTBody`) を追加。

---

## Phase 0 — signature 再確認 + skeleton 配置 📋

### スコープ

実装着手前に、Approach で参照する既存 lemma の signature が **olean レベルで実在** することを確認し、
skeleton 4 本 (`exists_hoeffding_minimizer_full_support` / `hoeffding_tradeoff_converse` /
`hoeffding_tradeoff_achievability` / `hoeffding_tradeoff`) を `:= by sorry` で配置して type-check を通す。

### ステップ

- [ ] 0-1 以下 7 本の signature を `lake env lean` で参照確認 (skeleton が通れば自動確認):
  - `exists_isHoeffdingLagrangeHyp_interior` (`HoeffdingMinimizerAttainment.lean:266`) —
    `0 < alpha → alpha ≤ klDivPmf P₂ P₁ → ∃ lam ∈ Ioc 0 1, IsHoeffdingLagrangeHyp P₁ P₂ alpha lam`
  - `IsHoeffdingLagrangeHyp.realises` / `.mem` (`HoeffdingInteriorGradientBody.lean:222`)
  - `hoeffdingTilt_pos` (`HoeffdingInteriorGradientBody.lean:112`)
  - `hoeffdingE2_minimizer_at_boundary_alpha_zero` (`HoeffdingSandwichBody.lean:168`)
  - `hoeffdingE2_minimizer_at_boundary_alpha_ge_kl` (`HoeffdingSandwichBody.lean:228`)
  - `sanov_ldp_lower_bound_pointwise` (`SanovLDPEquality.lean:1071`)
  - `stein_strong_lemma` (`StrongStein.lean:498`) + `csiszar_pythagoras_at_interior` (`HoeffdingInteriorBody.lean:245`)
- [ ] 0-2 skeleton を Write (在庫 §着手 skeleton をベースに、L-H4 補題を
  `exists_hoeffding_minimizer_full_support` に差し替え)。`headline` は `hoeffding_tradeoff_sandwich`
  への流し込みで即 close できるので 0-2 時点で sorry-free にしてよい。
- [ ] 0-3 LSP `<new-diagnostics>` で sorry warning のみ (error 0) を確認。

### Done 条件

skeleton が `lake env lean Common2026/Shannon/HoeffdingSandwichDischarge.lean` で sorry warning のみ。
残 sorry は `exists_hoeffding_minimizer_full_support` / `converse` / `achievability` の 3 本のみ
(headline は Phase 0 で close 済)。

### 撤退条件

skeleton が通らない (signature 不一致): まず import 漏れ / namespace open を疑う。それでも通らない
lemma があれば在庫を再確認し、該当 lemma を本 plan の参照から外す (Phase 1/2/3 の代替経路を判断ログに記録)。

---

## Phase 1 — `hoeffdingE2 = klDivPmf Qstar P₂` の 3-case 確立 📋

### スコープ

Approach §中核設計の統一補題 `exists_hoeffding_minimizer_full_support` を実装。
**abstract L-H4 を一切使わず**、3-case の既存 constructive 補題だけで close する。これが本 plan の心臓部。

### ステップ

- [ ] 1-1 `rcases lt_trichotomy alpha 0` ... ではなく **`rcases eq_or_lt_of_le h_alpha_nn`**
  で `alpha = 0` / `0 < alpha` に分け、後者を `rcases le_or_lt alpha (klDivPmf P₂ P₁)` で
  内部 / boundary に分ける (3-case)。
- [ ] 1-2 **case (a) α = 0**: K = {P₁} singleton。`hoeffdingE2_minimizer_at_boundary_alpha_zero`
  で full-support、`hoeffdingE2 = 0 = klDivPmf P₁ P₁` は `klDivPmf_self_eq_zero` +
  `hoeffdingConstraintSet_eq_singleton_at_alpha_zero` (`HoeffdingSandwichBody.lean:147`) から
  (alpha=0 collapse 補題が既にあれば直接流用)。Qstar := P₁。
- [ ] 1-3 **case (b) 0 < α ≤ klDivPmf P₂ P₁**: `exists_isHoeffdingLagrangeHyp_interior` で
  `⟨lam, hlam_Ioc, h_lag⟩` を取り、Qstar := `hoeffdingTilt P₁ P₂ lam`。`.mem` = membership,
  `.realises` = E2 等式, `hoeffdingTilt_pos` = full-support。
- [ ] 1-4 **case (c) klDivPmf P₂ P₁ < α**: `hoeffdingE2_minimizer_at_boundary_alpha_ge_kl`
  (`h_alpha_ge : klDivPmf P₂ P₁ ≤ alpha` を `.le` で供給) が triple を丸ごと返すので `exact`。
  Qstar := P₂。
- [ ] 1-5 3-case を `∃ Qstar ∈ K, ... ∧ (∀ a, 0 < Qstar a)` 形に統一して return。

### 依存補題 (file:line)

- `hoeffdingE2_minimizer_at_boundary_alpha_zero` (`HoeffdingSandwichBody.lean:168`)
- `hoeffdingConstraintSet_eq_singleton_at_alpha_zero` (`HoeffdingSandwichBody.lean:147`)
- `exists_isHoeffdingLagrangeHyp_interior` (`HoeffdingMinimizerAttainment.lean:266`)
- `IsHoeffdingLagrangeHyp` (`mem` / `realises`, `HoeffdingInteriorGradientBody.lean:222`)
- `hoeffdingTilt_pos` (`HoeffdingInteriorGradientBody.lean:112`)
- `hoeffdingE2_minimizer_at_boundary_alpha_ge_kl` (`HoeffdingSandwichBody.lean:228`)

### Done 条件

`exists_hoeffding_minimizer_full_support` が 0-sorry。推定 25-40 行。

### 撤退条件

case (a) で `hoeffdingE2 = 0 = klDivPmf P₁ P₁` の等式整形が想定外に長い (>15 行):
case (a) を `hoeffdingE2_minimizer_at_boundary_alpha_ge_kl` の α=0 sub-case として扱えるか確認
(`klDivPmf P₂ P₁ ≤ 0` は一般に偽なので不可、独立 case のまま)。それでも長ければ alpha=0 collapse の
専用補題を `HoeffdingSandwichBody.lean` 側に依頼 (本 plan は計画のみ、実装 agent が判断)。

---

## Phase 2 — converse `h_limsup ≤ E2` (Stein strong + Pythagoras) 📋

### スコープ

Phase 1 の full-support `Qstar` を使い、converse 仮定
`limsup (-(1/n) log steinTypeII_at_level_pmf) ≤ hoeffdingE2 P₁ P₂ alpha` を discharge。
在庫 §C の reuse ~80%。Phase 3 より低リスクなので先に着手。

### ステップ

- [ ] 2-1 Phase 1 の `Qstar` を取り出し (`obtain ⟨Qstar, hQs_mem, hQs_realises, hQs_pos⟩`)。
- [ ] 2-2 `pmfToMeasure` で `Qstar_meas := pmfToMeasure Qstar ...` / `P₂_meas := pmfToMeasure P₂ ...`。
  `IsProbabilityMeasure` は `pmfToMeasure_isProbabilityMeasure` (instance), `.real {a} = ·`は
  `pmfToMeasure_real_singleton`, `0 < ·.real {a}` は `pmfToMeasure_pos` (在庫 §B)。
- [ ] 2-3 `Qstar_meas ≪ P₂_meas` を full-support から (~5 行, `AbsolutelyContinuous`,
  在庫 §危険ボックス)。
- [ ] 2-4 IID プロセス boilerplate (`Ω := ℕ → α`, `μ := Measure.pi Qstar_meas`,
  `Xs i := fun ω => ω i`) — 在庫 §自作 6 (~20-30 行)。**他の Stein 利用箇所
  (`ChernoffPerTiltSanov` 等) に同型 boilerplate がある可能性 → 流用調査を最初に行う**。
- [ ] 2-5 `stein_strong_lemma` を起動 → `Tendsto (-(1/n) log steinOptimalBeta Qstar_meas P₂_meas n ε)
  atTop (𝓝 (klDiv Qstar_meas P₂_meas).toReal)`。
- [ ] 2-6 `steinTypeII_at_level_pmf P₁ P₂ n alpha` ↔ `steinOptimalBeta Qstar_meas P₂_meas n ε` の橋
  (在庫 §自作 4): pmf 形 `Finset` test ↔ Measure 形 `Set + MeasurableSet` test。
  **ここで任意 test の Type-I ≤ α が `Q ∈ K` に対応し、Pythagoras で E2 が支配**:
  `csiszar_pythagoras_at_interior` (interior case) / boundary case は E2 = 0 collapse。
- [ ] 2-7 3 段橋で `(klDiv Qstar_meas P₂_meas).toReal = klDivPmf Qstar P₂ = hoeffdingE2`
  (`hQs_realises` + `klDivSumForm_eq_toReal_klDiv` `Sanov.lean:252` + `klDivPmf_eq_log_diff_sum`
  `CsiszarProjection.lean:231` + `klDivSumForm_ofVec` def, 在庫 §B)。
- [ ] 2-8 `.eventually_le` で `∀ᶠ n, rate ≤ E2 + δ` ⇒ `limsup ≤ E2`。

### 依存補題 (file:line)

- `stein_strong_lemma` (`StrongStein.lean:498`)
- `csiszar_pythagoras_at_interior` (`HoeffdingInteriorBody.lean:245`) / E2 collapse (`HoeffdingSandwichBody.lean:194`)
- `klDivSumForm_eq_toReal_klDiv` (`Sanov.lean:252`), `klDivPmf_eq_log_diff_sum` (`CsiszarProjection.lean:231`)
- `pmfToMeasure_*` family (`HoeffdingTradeoff.lean:72/85` + `pmfToMeasure_pos`)
- `steinBetaSet_pmf` (`HoeffdingTradeoff.lean:109`) ↔ `steinBetaSet` (`Stein.lean:1139`)

### Done 条件

`hoeffding_tradeoff_converse` が 0-sorry。推定 80-120 行。

### 撤退条件

- **L-HP3**: 2-6 の pmf↔Measure test 橋 (`steinTypeII ↔ steinOptimalBeta`) が 30 行超:
  `stein_strong_lemma` の代わりに弱 `stein_lemma` (`Stein.lean:1390`) を流用、`1-ε` 因子を
  ε→0 外側ループで吸収 (~20 行追加)。判断ログに記録。
- 2-4 の IID boilerplate が 30 行超 & 流用先なし: `stein_strong_lemma` を呼ばず
  `steinTypicalSet_Q_prob_le` (`Stein.lean:341`) で per-type 上界を直接組む経路に切替。

---

## Phase 3 — achievability `E2 ≤ h_liminf` (Sanov lower + Type-I AEP) 📋

### スコープ

Phase 1 の full-support `Qstar` を使い、achievability 仮定
`hoeffdingE2 P₁ P₂ alpha ≤ liminf (-(1/n) log steinTypeII_at_level_pmf)` を discharge。
**本 plan で最も非自明・高リスク** (在庫 §自作 2/3/5、Type-I AEP が rabbit hole 候補)。
proof-log: yes (Type-I AEP の per-step を記録)。

### ステップ

- [ ] 3-1 Phase 1 の `Qstar` を取り出し (Phase 2 と同様)。`P₂_meas := pmfToMeasure P₂ ...`。
- [ ] 3-2 **acceptance region `E_n` の Finset 化** (在庫 §自作 2):
  `E_n := (univ : Finset (TypeCountIndex α n)).filter (fun c => decide ((fun a => (c a:ℝ)/n) ∈ K))`
  (classical decidable, `Classical.dec`, noncomputable 伝播)。
- [ ] 3-3 **`h_in_E : ∀ᶠ n, roundedTypeIndex Qstar n ∈ E_n`** (在庫 §自作 2):
  `(roundedTypeIndex Qstar n / n) ∈ K` の eventually 性を KL 連続 + `roundedTypeIndex_tendsto_vec`
  (`SanovLDPEquality.lean:297`) から (Qstar ∈ K の内点性 / rounding 誤差クリア, ~15-25 行)。
- [ ] 3-4 `sanov_ldp_lower_bound_pointwise (Q := P₂_meas) (P := Qstar) ... E_n h_in_E` を起動 →
  `-klDivSumForm_ofVec Qstar (P₂_meas.real {·}) ≤ liminf (1/n) log P₂^n(⋃ T_c)`。
  `P₂_meas.real {a} = P₂ a` を `pmfToMeasure_real_singleton` で書き換え、左辺を
  `-klDivPmf Qstar P₂ = -hoeffdingE2` に (`klDivPmf_eq_log_diff_sum` + `hQs_realises`, 在庫 §B)。
- [ ] 3-5 **Type-I 制御 AEP `∀ᶠ n, P₁^n(⋃ T_c) ≥ 1 - alpha`** (在庫 §自作 3, **最大 gap**):
  `⋃ T_c` (= K の type 近似 union) の補集合が `D(·‖P₁) > alpha` 域 → Sanov 上界で
  `P₁^n((⋃ T_c)^c) → 0` 以下、よって `P₁^n(⋃ T_c) ≥ 1 - α` 漸近。**既存 `typicalSet_prob_*`
  (`AEP.lean`) は entropy-band で set 形が違うので直接流用不可、自作 ~30-50 行**。
  落とし穴: `alpha` 下界の方向整合 (在庫 §自作 3)。proof-log にここの per-step を記録。
- [ ] 3-6 **`steinTypeII_at_level_pmf ≤ P₂^n(⋃ T_c)`** (在庫 §自作 5):
  `s := ⋃ T_c` が Type-I ≤ α の test なので `steinTypeII = sInf steinBetaSet_pmf ≤ P₂^n(s)`。
  `P₂^n(⋃ T_c).toReal = Σ_{x∈Finset 化} ∏ P₂(x i)` (`Measure.pi_singleton` + `ENNReal.toReal_prod`,
  在庫 §E)。
- [ ] 3-7 3-4 (liminf 下界) + 3-6 (steinTypeII ≤ P₂^n) を組み、符号反転して
  `E2 ≤ liminf (-(1/n) log steinTypeII)` に整地 (`Filter.liminf` の単調性 + `Tendsto.eventually_ge`,
  在庫 §E)。

### 依存補題 (file:line)

- `sanov_ldp_lower_bound_pointwise` (`SanovLDPEquality.lean:1071`)
- `roundedTypeIndex` / `roundedTypeIndex_tendsto_vec` (`SanovLDPEquality.lean:111/297`)
- `typeClassByCount` (`SanovLDP.lean:82`), `TypeCountIndex` (`SanovLDP.lean:55`)
- `sanov_ldp_upper_bound` (`SanovLDP.lean:471`, Type-I AEP 補集合の上界に流用候補)
- `klDivPmf_eq_log_diff_sum` (`CsiszarProjection.lean:231`), `klDivSumForm_ofVec` (`KLDivContinuous.lean:31`)
- `sum_prod_pi_eq_pow_sum` (`HoeffdingTradeoff.lean:120`), `steinBetaSet_pmf` (`HoeffdingTradeoff.lean:109`)
- `typicalSet_prob_*` (`AEP.lean:375/1403`, **参照テンプレのみ, 直接流用不可**)

### Done 条件

`hoeffding_tradeoff_achievability` が 0-sorry。推定 120-180 行。

### 撤退条件 (段階的, 在庫 §撤退ライン)

- **L-HP1**: 3-5 Type-I AEP plumbing が 30 行超 → degenerate Sanov (`P := P₁, Q := P₁`,
  `klDivPmf P₁ P₁ = 0`) 自己呼び出しで書き直し。
- **L-HP2**: 3-5 が 50 行超 → `stein_achievability` の Qstar 流用に縮退、または下記 **L-H4-FB** 発動。
- **L-HP2'** (acceptance region): 3-2/3-3 の Finset 化 + Decidable 性が 40 行超 →
  `Finset.univ.filter (Classical.dec ...)` で全 noncomputable 化 (在庫 §自作 2)。

---

## Phase 4 — headline hypothesis-free 統合 📋

### スコープ

Phase 2 (`converse`) + Phase 3 (`achievability`) を `hoeffding_tradeoff_sandwich`
(`HoeffdingSandwich.lean:290`, boundedness 2 本は内部 discharge 済) に流し込み、headline
`hoeffding_tradeoff` を hypothesis-free で組み立てる。在庫 §着手 skeleton の `hoeffding_tradeoff`
の組み立てそのまま (Phase 0 で既に close 済なら本 Phase は確認のみ)。

### ステップ

- [ ] 4-1 `hoeffding_tradeoff_sandwich P₁ P₂ ... h_alpha_nn h_alpha_lt
  (achievability ...) (converse ...)` で `:= ` 直接定義。
- [ ] 4-2 境界条件は `alpha < 1` のみであることを確認 (`alpha < klDivPmf P₁ P₂` は不要、
  3-case が boundary を吸収する)。
- [ ] 4-3 旧 `hoeffding_tradeoff_with_hypothesis` (`HoeffdingTradeoff.lean:296`) から本 headline への
  pointer (deprecated コメント or corollary) を残すか実装 agent が判断。

### Done 条件

`hoeffding_tradeoff` が 0-sorry hypothesis-free。ファイル全体が
`lake env lean Common2026/Shannon/HoeffdingSandwichDischarge.lean` で silent。

---

## Phase V — clean check + `Common2026.lean` 編入 (オーケストレータ) 📋

- [ ] V-1 `lake env lean Common2026/Shannon/HoeffdingSandwichDischarge.lean` silent (0 sorry / 0 error)。
- [ ] V-2 `Common2026.lean` に `import Common2026.Shannon.HoeffdingSandwichDischarge` 追記
  (既存 Hoeffding import 群の直後)。
- [ ] V-3 `lake env lean Common2026.lean` で全体 silent 確認。
- [ ] V-4 本 plan 進捗ブロックを `✅` に更新、判断ログに publish 完了 append。
  親 plan `hoeffding-tradeoff-moonshot-plan.md` の Phase C/D を `✅` (or 縮退範囲を記録) に更新。

---

## 撤退ライン

第一目標は **3-case 全部 genuine で hypothesis-free**。段階的着地点:

- **L-H4-FB (boundary fallback)**: Phase 3 の Type-I AEP (3-5) が rabbit hole 化した場合、
  少なくとも **case (c) `klDivPmf P₂ P₁ ≤ α` の boundary** は `hoeffdingE2 = 0` collapse
  (`hoeffdingE2_eq_zero_at_alpha_ge_kl` `HoeffdingSandwichBody.lean:194`) で achievability/converse が
  degenerate に簡単化する可能性が高い (`steinTypeII → 1`, rate → 0)。**最悪この boundary case
  だけ hypothesis-free + 内部/α=0 は honest 仮定 (明示 signature の `h_liminf`/`h_limsup`
  pass-through、`:= True` 不使用) で残す**。
  - 縮退後 publish 単位: `hoeffding_tradeoff_at_boundary` (`alpha ≥ klDivPmf P₂ P₁` の
    hypothesis-free Tendsto) + 内部 hypothesis 形 `hoeffding_tradeoff_interior_with_hypothesis`。
- **L-HP1 / L-HP2 / L-HP2'**: Phase 3 の自作 plumbing 肥大ライン (各 Phase 3 §撤退条件)。
- **L-HP3**: Phase 2 の Stein strong → 弱 Stein + ε 外側ループ縮退 (Phase 2 §撤退条件)。

**Phase 1 が hypothesis-free の鍵**: L-H4 (`hoeffdingE2_minimizer_full_support` abstract gradient 補題)
を **構成的 3-case で完全回避済**なので、変分側 (full-support 供給) は撤退不要。残るリスクは
**Phase 3 の Type-I AEP のみ** に局所化されている。

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(計画起草) L-H4 を構成的 3-case で回避する設計を採用** — 親 plan は achievability/converse の
   full-support 供給を abstract `hoeffdingE2_minimizer_full_support` (log-singularity gradient,
   親 plan 判断ログ #2 で defer) に依存していた。本 plan では `alpha` を `klDivPmf P₂ P₁` 境界で
   3-case 分割し、各 case の **既に 0-sorry 完成済の constructive minimizer 補題**
   (`hoeffdingE2_minimizer_at_boundary_alpha_zero` / `exists_isHoeffdingLagrangeHyp_interior` /
   `hoeffdingE2_minimizer_at_boundary_alpha_ge_kl`) で full-support + E2 等式を供給する設計に変更。
   これにより L-H4 を回避し、残リスクを Phase 3 の Type-I AEP のみに局所化。
2. **(計画起草) Phase 2 (converse) を Phase 3 (achievability) より先に着手** — 在庫 §C で converse は
   `stein_strong_lemma` 流用 reuse ~80%、achievability は Type-I AEP の自作が必要 (~75%)。
   reuse の高い converse を先に通して Sanov/Stein plumbing (pmf↔Measure 橋, IID boilerplate) を
   検証してから achievability に進む。
3. **(計画起草) headline の境界条件を `alpha < 1` に確定** — `hoeffding_tradeoff_sandwich`
   (`HoeffdingSandwich.lean:290`) の要求が `alpha < 1` のみ。3-case が boundary 域も吸収するため
   親 plan / 在庫 §主定理最終形にあった `alpha < klDivPmf P₁ P₂` strict 仮定は **headline には不要**
   (Phase 1 の case 分岐内部でのみ `klDivPmf P₂ P₁` 境界を使う)。
4. **(実装中、2026-05-21) 🛑 DEF-FLAW 発見 — headline は数学的に偽、Phase 3/4 無効化** —
   Phase 2 着手時に `steinTypeII_at_level_pmf` の定義 (`HoeffdingTradeoff.lean:109-116`、制約
   `(1 - ∑_{x∈s} ∏ P₁(xᵢ)) ≤ alpha` = **定数** Type-I *確率* level) を精査した結果、これは Hoeffding
   tradeoff 曲線が要求する **指数** Type-I level (`α_n = exp(-nr)`、= 経験分布の KL-sublevel
   acceptance region) と別物と判明。一方 `hoeffdingE2` (`Chernoff.lean:265`) は `inf{KL(Q‖P₂) :
   KL(Q‖P₁) ≤ alpha}` で KL(指数)-level。固定 α の rate は Stein lemma で `→ D(P₁‖P₂) = E₂(0)` に
   収束 (α 非依存)、α>0 では `E₂(alpha) < E₂(0)` ⟹ headline `rate → E₂(alpha)` は **偽**。α=0 でも
   `steinTypeII ≡ 1` (唯一の Type-I-exact-0 test は `s=univ`) ⟹ `rate ≡ 0 ≠ D > 0` で反例。
   **対応**: 偽 goal を `sorry` せず、genuine pieces のみ着地 (Phase 1 minimizer / boundary
   achievability / honest wrapper、0 sorry)。Phase 3 (Sanov Type-I AEP) / Phase 4 (統合) は
   **無効化**。full discharge には operational 量を指数 level へ再定義する **別サブ計画
   `hoeffding-exponent-level-redef-plan.md`** が必要 (`steinTypeII_exp P₁ P₂ n r := sInf{β | ∃ s,
   (1-P₁ⁿ(s)) ≤ exp(-n·r) ∧ β = P₂ⁿ(s)}` 形 + sandwich machinery の再導出 + Sanov 両側)。これは
   V1 fisherInfo / 旧 Shannon-Hartley 循環と同種の「定義が wrong target を実現」flaw。
