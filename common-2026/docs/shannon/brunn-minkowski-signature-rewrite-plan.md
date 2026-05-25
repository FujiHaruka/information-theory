# Shannon: BrunnMinkowski — `entropy_eq_logVolume_iff_uniform` + `brunn_minkowski_linear_from_prekopa_leindler` signature rewrite plan

> **Parent**: [`brunn-minkowski-sorry-migration-plan.md`](brunn-minkowski-sorry-migration-plan.md) §「Phase 2.3 — 第一選択 (定義書換) を試みる」の **後追い独立 plan**
> + handoff [`.claude/handoff-sorry-migration.md`](../../.claude/handoff-sorry-migration.md) §「Round 2 残課題 follow-up」3 件目
> Pilot references:
> [`hoeffding-sorry-migration-plan.md`](hoeffding-sorry-migration-plan.md) / [`chernoff-sorry-migration-plan.md`](chernoff-sorry-migration-plan.md)
> (Pattern E retract-candidate + Pattern F tier 5 inline judgment).

## 進捗

- [ ] Phase 0 — 規模見積もり + verbatim downstream consumer 確認 📋
- [ ] Phase 1 — `entropy_eq_logVolume_iff_uniform` signature rewrite (single sweep) 📋
- [ ] Phase 2 — `brunn_minkowski_linear_from_prekopa_leindler` signature rewrite (single sweep) 📋
- [ ] Phase V — verify (`lake env lean` 0 errors + honesty-auditor 独立検証) 📋

## ゴール / Approach

### ゴール

`Common2026/Shannon/BrunnMinkowskiFunctional.lean` の 2 declaration が現状 `@residual(defect:false-statement)` (tier 5) で残置している状態を、**第一選択 (signature 改変による linkage hypothesis 追加 + body sorry)** に移行する。両者とも Round 2 sorry-migration で「定義書換は abstract-vol convention の整合性を壊すため第二選択 fallback」と判定済 (Round 3 で `defect:circular` → `defect:false-statement` に reason 修正のみ実施)。本 plan はその第一選択完遂のための **独立 sweep**。

| # | file:line | decl 名 | 現状タグ | 残置理由 (Round 2/3 docstring 記録) |
|---|---|---|---|---|
| 1 | `BrunnMinkowskiFunctional.lean:509` | `brunn_minkowski_linear_from_prekopa_leindler` | `@residual(defect:false-statement)` | `(volA, volB, volAB)` が free real numbers で linkage hyp 不在、`volA=volB=1, volAB=1` で `2 ≤ 1` 反証可能。abstract-vol convention の整合性を壊さないため Round 3 では第二選択据置。 |
| 2 | `BrunnMinkowskiFunctional.lean:608` | `entropy_eq_logVolume_iff_uniform` | `@residual(defect:false-statement)` | `(μ, h, vol)` を constrain する linkage hyp 不在 (`hvol : 0 < vol` のみ)、任意 μ/h/vol で `h μ = Real.log vol` 不成立。Round 3 では第二選択据置。 |

### Approach (全体戦略)

**核となる observation**: 既存 file (`BrunnMinkowski.lean:159`) に `IsUniformOnEntropyLogVolHypothesis n h μ vol := h μ = Real.log vol` が登録済 (Round 1 で既に load-bearing predicate として `@audit:retract-candidate(load-bearing-predicate)` 化対象)。`entropy_eq_logVolume_iff_uniform` をこの predicate consumer に書換えると **再び循環** (`:= h_unif` で着地、tier 5 circular)。

→ 第一選択の真の意味は **「linkage hypothesis としての uniform 性は load-bearing 化しない、actual measure `μ` を `uniformOn` (Mathlib) で固定し、`vol = (volume of convex body)` を `(volume A).toReal` 形で linkage」**。`BrunnMinkowskiClosure.lean:373` の `brunn_minkowski_volume_indicator` が既に同 convention で publish 済なので、その流儀に揃える。

具体的には:

1. **decl #2 (`entropy_eq_logVolume_iff_uniform`)**: 結論を `characterization 形 (↔)` に書換。signature を `μ = Measure.uniform (convex body of volume vol)` (or 同等の Mathlib `IsUniform`) を **load-bearing hyp として bundling しない** linkage 形 (Mathlib-shape-driven) に変更し、body は Mathlib 壁 (`continuous-aep` / `n-dim-gaussian-aep` 系または独立 `wall:uniform-max-entropy-on-convex-body`) で sorry 化。
2. **decl #1 (`brunn_minkowski_linear_from_prekopa_leindler`)**: signature に `volA = (volume A).toReal` 等の linkage hypothesis を Mathlib `MeasureTheory.volume` ベースで追加 (Closure plan の §F convention)。body は **Mathlib 壁** (`wall:bm-convex-body-sqrt` の linear specialization、または独立 `wall:bm-additive-convex-body`) で sorry 化。

両者とも **新規 wall promote** が必要になる可能性がある (Phase 0 で確定)。Phase 2 で promote 要否を実装と並行判定。

### 撤退ライン

第一選択での body sorry 化が **当該 session 内で完遂不能** な場合 (例: linkage hyp 形に書換えると downstream consumer の re-verify chain が予想外に長い、または abstract-vol convention の整合性が他の P-1/P-2 系 10+ declaration に波及して 1 PR scope を超える) は、Phase 0 段階で `Round 5 大 plan` (BM family abstract-vol convention 全体 honest 化) として scope 拡張判断する。本 plan は **当該 2 declaration 限定 1 PR scope** をデフォルトとし、scope 拡張時は本 plan を **discontinue** + 大 plan に統合。

## SoT

- **コード** (`docs/audit/audit-tags.md`「SoT 階層」): `Common2026/Shannon/BrunnMinkowskiFunctional.lean:509, :608` の `@residual` タグが現状の source of truth。本 plan 完了時に `@residual(defect:false-statement)` → `@residual(wall:<新規 wall name>)` または `@residual(plan:brunn-minkowski-signature-rewrite-plan)` に書換、signature を linkage hyp 形に改変。
- **vocab register**: `docs/audit/audit-tags.md` Wall name register / Proposed (Phase 2 で promote 判断)。

## Phase 0 — 規模見積もり + verbatim 確認 (in-mind: docs-only) 📋

`proof-log: no` (mechanical inventory)。

- [ ] **0.1** 2 declaration の verbatim location 再確認 (line drift 防止):
  ```bash
  rg -n 'theorem entropy_eq_logVolume_iff_uniform|theorem brunn_minkowski_linear_from_prekopa_leindler' Common2026/Shannon/BrunnMinkowskiFunctional.lean
  ```
  本 plan 起草時 (2026-05-26): `:509` + `:608`。
- [ ] **0.2** Downstream consumer rg (verbatim 件数 → scope 確認):
  ```bash
  rg -n 'entropy_eq_logVolume_iff_uniform|brunn_minkowski_linear_from_prekopa_leindler' Common2026/ --type lean
  ```
  本 plan 起草時 verbatim 結果: **2 hits、両者とも自己定義行のみ** = file 内 / file 外 consumer 0 件。signature 改変の re-verify 範囲は `BrunnMinkowskiFunctional.lean` 単体に限定。
- [ ] **0.3** 関連 linkage predicate の verbatim 確認:
  - `IsUniformOnEntropyLogVolHypothesis` (`BrunnMinkowski.lean:159`): `Prop := h μ = Real.log vol`。これを decl #2 の linkage hyp に **そのまま使うと再び `:= h_unif` 循環** (tier 5 → tier 5 横移動)。
  - `BrunnMinkowskiClosure.lean:373 brunn_minkowski_volume_indicator`: linkage convention `(volume A).toReal ^ lam * ... ≤ (volume (lam • A + (1-lam) • B)).toReal`。**この convention が本 plan の参照モデル**。
- [ ] **0.4** Mathlib 壁の候補確認 (loogle):
  - `MeasureTheory.IsUniform` / `Measure.uniformOn` 系の Mathlib 在庫 (decl #2 用)
  - `MeasureTheory.brunnMinkowski` / Brunn-Minkowski additive form の Mathlib 在庫 (decl #1 用)
  - 両者とも `Found 0` 想定 (本 plan 起草時の loogle 単発確認で `Brunn-Minkowski` は Mathlib 不在 — `BrunnMinkowskiFunctional.lean:33` の docstring 「Prékopa-Leindler は本リポジトリ範囲では未本格化」が SoT)
- [ ] **0.5** 撤退ライン判定 — Phase 0 完了時点で次のいずれかなら **Round 5 大 plan に scope 拡張**:
  - downstream consumer chain が **3 file 横断 + 5 declaration 以上** に膨らんだ (本 plan 起草時 verbatim では **0 件** ゆえ trigger 不発)
  - linkage hyp の形が他の P-1/P-2 系 declaration (`prekopa_leindler_geometric_mean_form` `:480` / `brunn_minkowski_convex_body` `BrunnMinkowski.lean:247` 等) と整合せず **convention 拡張で 10+ declaration touch 必要** (Phase 2 で実装上の判定)
- [ ] **0.6** Phase 0 完了時 docs-only commit (本 plan + audit-tags.md Proposed への候補 wall name 追記)。

### Phase 0 中央予測

- **scope**: 1 file (`BrunnMinkowskiFunctional.lean`) 単体、追加 import 0 件 (linkage hyp 形は既存 `MeasureTheory.volume` で表現可能、`Measure.uniformOn` 必要なら 1 行 import 追加)
- **中央予測 sorry 数**: 2 件 (両 declaration とも body sorry 化、`@residual` 形は Phase 2 で確定)
- **shared sorry 補題化必要性**: **暫定 no** (両 declaration は独立、共有 helper 不要)。ただし Phase 2 で `wall:bm-convex-body-sqrt` / `wall:uniform-max-entropy-on-convex-body` 新 wall promote が浮上した場合は **promote → audit-tags.md Wall name register 更新** (Pattern E retract-candidate 拡張ルート)
- **撤退ライン flag**: **no** (Phase 0 verbatim 確認で consumer 0 件、scope 拡張 trigger 不発の見込み)

## Phase 1 — `entropy_eq_logVolume_iff_uniform` signature rewrite 📋

`proof-log: yes` (`docs/shannon/proof-log-bm-signature-rewrite-phase1.md`)。signature 改変 + 結論型書換 (`=` → `↔`) の境界判定が走るため。

### Phase 1 設計 (Approach)

現状 (`:608`):

```lean
theorem entropy_eq_logVolume_iff_uniform
    {n : ℕ} (μ : Measure (Fin n → ℝ))
    (h : Measure (Fin n → ℝ) → ℝ)
    (vol : ℝ) (hvol : 0 < vol) :
    h μ = Real.log vol := by
  sorry
-- @residual(defect:false-statement)
```

**Mathlib-shape-driven 書換** (CLAUDE.md「Mathlib-shape-driven Definitions」適用):

1. **第一選択 — `↔` characterization 形** (declaration 名と本来の textbook 主張 (Cover-Thomas 17.9.4) に整合):
   ```lean
   theorem entropy_eq_logVolume_iff_uniform
       {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
       (h : Measure (Fin n → ℝ) → ℝ)
       (A : Set (Fin n → ℝ)) (hA_conv : Convex ℝ A) (hA_vol : 0 < (volume A).toReal) :
       (∀ s, μ s = volume (s ∩ A) / volume A) ↔ h μ = Real.log (volume A).toReal := by
     sorry
   -- @residual(wall:uniform-max-entropy-on-convex-body)
   ```
   linkage: `μ` が actual uniform on convex body `A`、`vol = (volume A).toReal` で identification。Mathlib 壁: uniform measure の characterization + max-entropy 性質の n-dim 形 (Mathlib 不在)。

2. **第二選択 fallback — load-bearing 化を避ける単純 sorry 化**: linkage を Mathlib API で書けない場合は signature を:
   ```lean
   theorem entropy_eq_logVolume_iff_uniform
       {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
       (h : Measure (Fin n → ℝ) → ℝ)
       (A : Set (Fin n → ℝ)) (hA_conv : Convex ℝ A) (hA_vol : 0 < (volume A).toReal)
       (hμ_uniform : ∀ s, μ s = volume (s ∩ A) / volume A) :
       h μ = Real.log (volume A).toReal := by
     sorry
   -- @residual(plan:brunn-minkowski-signature-rewrite-plan)
   ```
   linkage hyp は `hμ_uniform` (regularity の延長、load-bearing でない — μ の identification を表す equational hyp で **conclusion-as-hypothesis ではない**)。`@residual` は plan slug。

### Phase 1 step

- [ ] **1.1** 既存 `entropy_eq_logVolume_iff_uniform` の docstring 全文 (`:588-:607`) を **proof-log に verbatim 退避** (honesty-auditor の Round 2 follow-up 散文を歴史記録として保存)。
- [ ] **1.2** signature を上記第一選択形に書換。linkage hyp として `A : Set (Fin n → ℝ)`、`hA_conv : Convex ℝ A`、`hA_vol : 0 < (volume A).toReal` を追加、結論を `↔` 形に書換 (`(∀ s, μ s = volume (s ∩ A) / volume A) ↔ h μ = Real.log (volume A).toReal`)。
- [ ] **1.3** body は `sorry` 単独行。`@residual(wall:uniform-max-entropy-on-convex-body)` を docstring 末尾に付与 (新規 wall name)。
- [ ] **1.4** 新規 wall name の **Proposed → Register promote**: `docs/audit/audit-tags.md` Wall name register に `uniform-max-entropy-on-convex-body` を **新規 entry 追加** (本 plan 完了で初出となる新 wall、`Ch.17.9 Cover-Thomas 17.9.4` 関連)。promote 判定基準は audit-tags.md「promote 判定基準」を満たす: (1) 該当 declaration が wall として再利用 (decl #2 1 件のみで現状 only) ではないが、(2) `plan:<slug>` よりも wall 化が結論型の **Mathlib 壁としての永続性** と整合 → promote 採用。
- [ ] **1.5** linker error (`Convex` / `volume` 未 import) 解消のために必要 import:
  - `Mathlib.Analysis.Convex.Basic` (既存 file の import 確認)
  - `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` (`volume` for `Fin n → ℝ`)
  - 既存 import の確認は **Phase 1.5 で verbatim 実施** (`rg '^import' Common2026/Shannon/BrunnMinkowskiFunctional.lean`)
- [ ] **1.6** `lake env lean Common2026/Shannon/BrunnMinkowskiFunctional.lean` で type-check done 確認 (0 errors + 1 sorry warning)。Pattern A (stale olean) の懸念: signature 改変が広範な dependent に影響しないことが Phase 0.2 で確認済 (consumer 0 件) ゆえ `lake build` 不要。
- [ ] **1.7** **Inline alert チェック**: signature 書換後の linkage hyp `hμ_uniform : (∀ s, μ s = volume (s ∩ A) / volume A)` が **conclusion-as-hypothesis ではない** ことを確認 — 結論 (`h μ = Real.log ...`) と全く異なる形 (`μ s = ...` という measure identification) ゆえ load-bearing predicate bundling ではない。**load-bearing 判定**: `IsUniformOnEntropyLogVolHypothesis` (= 結論型 verbatim) を avoid している判断を docstring に 1 行明示。
- [ ] **1.8** Phase 1 完了時 honesty-auditor 独立起動 (`general-purpose` subagent w/ CORE doctrine inline)。判定 focus:
  - (a) 新 signature の linkage hyp `hμ_uniform` が conclusion-as-hypothesis ではないか
  - (b) `@residual(wall:uniform-max-entropy-on-convex-body)` の新規 wall promote が audit-tags.md 整合
  - (c) `↔` characterization 形が CLAUDE.md「Mathlib-shape-driven Definitions」と整合 (結論型が Mathlib lemma の入力形と直接接続できる shape)

### Phase 1 DoD

- `BrunnMinkowskiFunctional.lean:608` の `@residual(defect:false-statement)` が 0 件、`@residual(wall:uniform-max-entropy-on-convex-body)` 1 件で sorry 1 件。
- `lake env lean` 0 errors (1 sorry warning 許容)。
- `docs/audit/audit-tags.md` Wall name register に新規 entry。
- honesty-auditor verdict 確認後 commit。

## Phase 2 — `brunn_minkowski_linear_from_prekopa_leindler` signature rewrite 📋

`proof-log: yes` (`docs/shannon/proof-log-bm-signature-rewrite-phase2.md`)。

### Phase 2 設計 (Approach)

現状 (`:509`):

```lean
theorem brunn_minkowski_linear_from_prekopa_leindler
    {n : ℕ} (A B : Set (Fin n → ℝ))
    (volA volB volAB : ℝ)
    (hvolA : 0 ≤ volA) (hvolB : 0 ≤ volB) (hvolAB : 0 ≤ volAB) :
    volA + volB ≤ volAB := by
  sorry
-- @residual(defect:false-statement)
```

**Mathlib-shape-driven 書換**: linkage hyp として `volA = (volume A).toReal` 等を **equational hyp** で追加し、結論を `(volume A).toReal + (volume B).toReal ≤ (volume (A + B)).toReal` 形に書換。`Closure.lean:373 brunn_minkowski_volume_indicator` の convention (`(volume A).toReal ^ lam * ...`) と整合。

```lean
theorem brunn_minkowski_linear_from_prekopa_leindler
    {n : ℕ} (A B : Set (Fin n → ℝ))
    (hA_conv : Convex ℝ A) (hB_conv : Convex ℝ B)
    (hA_meas : MeasurableSet A) (hB_meas : MeasurableSet B)
    (hAB_meas : MeasurableSet (A + B)) :
    (volume A).toReal + (volume B).toReal ≤ (volume (A + B)).toReal := by
  sorry
-- @residual(wall:bm-additive-convex-body)
```

linkage: `volA / volB / volAB` の自由 real 引数を削除、Mathlib `MeasureTheory.volume` で identification。convex + measurable は regularity hyp (load-bearing でない、Mathlib の Brunn-Minkowski 系で標準的に必要)。**Mathlib 壁**: Brunn-Minkowski additive 形 (convex body の体積和 ≤ Minkowski sum 体積) が Mathlib 不在 (Phase 0.4 で確認)。

### Phase 2 step

- [ ] **2.1** 既存 docstring 全文 (`:487-:507`) を proof-log に verbatim 退避。
- [ ] **2.2** signature を上記形に書換。引数表:

  | 旧引数 | 旧型 | 処理 |
  |---|---|---|
  | `(A B : Set (Fin n → ℝ))` | (regularity 引数) | **保持** |
  | `(volA volB volAB : ℝ)` | (free scalar、linkage 不在で false-statement の根源) | **削除** |
  | `(hvolA hvolB hvolAB : 0 ≤ _)` | (削除済 free scalar の非負条件、不要) | **削除** |
  | 新規 `(hA_conv : Convex ℝ A)` | regularity | **追加** |
  | 新規 `(hB_conv : Convex ℝ B)` | regularity | **追加** |
  | 新規 `(hA_meas / hB_meas / hAB_meas : MeasurableSet _)` | regularity | **追加** (Minkowski sum 可測性は `IsMinkowskiSumMeasurableHypothesis` と同等 — load-bearing ではない、Mathlib の `Convex.measurableSet` 系で discharge 可能) |

- [ ] **2.3** body は `sorry` 単独行。`@residual(wall:bm-additive-convex-body)` を docstring 末尾に付与 (新規 wall name)。
- [ ] **2.4** 新規 wall name promote: `docs/audit/audit-tags.md` Wall name register に `bm-additive-convex-body` 新規 entry 追加 (Phase 1 と同じ promote 判定ロジック)。
- [ ] **2.5** import 確認 + 必要なら追加 (`Mathlib.Analysis.Convex.Basic`, `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`, `Mathlib.Algebra.Group.Pointwise.Set.Basic` for `A + B`).
- [ ] **2.6** `lake env lean Common2026/Shannon/BrunnMinkowskiFunctional.lean` で type-check done (0 errors + 1 sorry warning + Phase 1 の 1 sorry = 計 2 sorry warnings)。
- [ ] **2.7** **Inline alert チェック**: 新 signature の hyp が **全て regularity** であることを確認 — `Convex` / `MeasurableSet` は precondition、結論型 (`(volume A).toReal + (volume B).toReal ≤ (volume (A + B)).toReal`) と全く異なる shape ゆえ load-bearing bundling ではない。
- [ ] **2.8** Phase 2 完了時 honesty-auditor 独立起動。判定 focus:
  - (a) 新 signature の hyp が全て regularity (load-bearing ではない)
  - (b) `@residual(wall:bm-additive-convex-body)` の新規 wall promote が audit-tags.md 整合
  - (c) `(volume _).toReal` convention が `Closure.lean:373` と整合

### Phase 2 DoD

- `BrunnMinkowskiFunctional.lean:509` の `@residual(defect:false-statement)` が 0 件、`@residual(wall:bm-additive-convex-body)` 1 件で sorry 1 件。
- `lake env lean` 0 errors (2 sorry warnings 許容 = Phase 1 + Phase 2)。
- `docs/audit/audit-tags.md` Wall name register に新規 entry 2 件 (`uniform-max-entropy-on-convex-body` + `bm-additive-convex-body`)。
- honesty-auditor verdict 確認後 commit。

## Phase V — verify (全体最終確認) 📋

`proof-log: no` (mechanical verify)。

- [ ] **V.1** `lake env lean Common2026/Shannon/BrunnMinkowskiFunctional.lean` 最終 0 errors 確認。
- [ ] **V.2** タグ集計 (canonical declaration-direct grep, `docs/audit/sorry-migration-runbook.md` Pattern D):
  ```bash
  rg -n '@residual\(defect:false-statement\)' Common2026/Shannon/BrunnMinkowskiFunctional.lean
  ```
  → 期待: **0 hits** (Phase 1 + Phase 2 で 2 件削減)。
  ```bash
  rg -n '@residual\(wall:uniform-max-entropy-on-convex-body|@residual\(wall:bm-additive-convex-body' Common2026/Shannon/BrunnMinkowskiFunctional.lean
  ```
  → 期待: **2 hits** (各 1 件)。
- [ ] **V.3** downstream consumer chain re-verify: Phase 0.2 で 0 件確認済ゆえ単体 file 検証で十分だが、念のため `lake env lean Common2026/Shannon/BrunnMinkowskiConcavity.lean` + `Common2026/Shannon/BrunnMinkowskiClosure.lean` を spot-check (両者は `BrunnMinkowskiFunctional` を直接 / transitive に import、import side-effect の `unknown identifier` 等を弾く)。
- [ ] **V.4** `Common2026.lean` の import 行は **変更なし** ことを確認 (本 plan は既存 file の signature 改変のみ、新 file 追加なし)。
- [ ] **V.5** handoff 更新: `.claude/handoff-sorry-migration.md` §「Round 2 残課題 follow-up」3 件目「BM `entropy_eq_logVolume_iff_uniform` + `brunn_minkowski_linear_from_prekopa_leindler` signature rewrite」を ✅ 完了 marker に置換、本 plan の終了 commit を参照する 1 行追記。
- [ ] **V.6** sibling plan `brunn-minkowski-sorry-migration-plan.md` Phase 2.3 の「**第一選択 (定義書換)** を試みる」散文に「→ 本 task は `brunn-minkowski-signature-rewrite-plan.md` で完遂済 (2026-05-26)」の 1 行 cross-ref を追加 (sibling plan は touch しない判断もあり — Phase V で planner が判定)。

### Phase V DoD

- `@residual(defect:false-statement)` 件数: file 全体で **0** (本 plan 完遂)。
- 新規 wall `uniform-max-entropy-on-convex-body` + `bm-additive-convex-body` が audit-tags.md Wall name register で formally registered。
- handoff の Round 2 残課題 follow-up #3 が closed。
- session 末で squashed commit + push (CLAUDE.md「Commits」)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-26 起草時**: 当初 brief 「もし 2 declaration が Round 3 BMClosure sweep で既に sorry-based migrated 済なら short plan で OK」を verbatim 確認した結果、**両 declaration とも Round 3 で第二選択 fallback (tier 5 `@residual(defect:false-statement)` 据置)**。第一選択 (signature 改変 + body sorry) は **未着手**、本 plan が第一選択完遂のための初回 plan となる。short plan ではなく Phase 0/1/2/V の標準構造で起草。
2. **2026-05-26 起草時 (撤退ライン flag 判定)**: Phase 0.2 verbatim rg で **downstream consumer 0 件** (両 declaration とも自己定義行のみ hit)。runbook の 3+ file 横断 / 5+ declaration trigger に該当せず、scope 拡張不要。Round 5 大 plan への scope 拡張は **不発**、本 plan の 1 PR scope で完遂可能。
3. **2026-05-26 起草時 (新規 wall promote 判断)**: 両 declaration とも Mathlib 壁 (`uniform-max-entropy-on-convex-body` / `bm-additive-convex-body`) を **新規 promote** で導入予定。audit-tags.md Wall name register の Round 4 末状態 (`stam` / `csiszar` / `n-dim-gaussian-aep` / `sphere-volume` / `continuous-aep` / `nyquist-2w-dof` / `multivariate-mi` / `joint-typicality-multi` / `epi-n-dim` / `fourier`) に追加。`epi-n-dim` と意味的に近接するが、`epi-n-dim` は「n 次元 EPI / n-dim PL の slice 解析」を指し、本 plan の wall は「convex body uniform max-entropy 性質」と「BM additive form」で意味が異なるため別 entry。
