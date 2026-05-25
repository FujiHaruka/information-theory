# Shannon: BrunnMinkowski `@audit:suspect` → sorry-based migration plan

> **Parent**: [`brunn-minkowski-moonshot-plan.md`](brunn-minkowski-moonshot-plan.md) §残① / pass-through publish 部分
> + sibling [`brunn-minkowski-closure-plan.md`](brunn-minkowski-closure-plan.md) (Fubini route, DONE except Phase V cleanup)
> + sibling [`brunn-minkowski-from-epi-discharge-plan.md`](brunn-minkowski-from-epi-discharge-plan.md) (EPI route, 未着手)
> 本 plan は **proof completion ではなく `@audit:suspect` / `@audit:staged` / `@audit:defer` / 散文 `🟢ʰ` / `@audit:defect(circular)` 語彙の honesty 強化**
> (`docs/audit/audit-tags.md`「Deprecated」+「移行レシピ」+ tier 5 defect の sorry-based 後継化) を目的とする独立 workstream。
> Pilot references: [`hoeffding-sorry-migration-plan.md`](hoeffding-sorry-migration-plan.md) /
> [`cramer-sorry-migration-plan.md`](cramer-sorry-migration-plan.md) /
> [`wynerziv-sorry-migration-plan.md`](wynerziv-sorry-migration-plan.md)。

## Context

### なぜ BrunnMinkowski を sweep するか

`docs/audit/sorry-migration-runbook.md`「並列実行候補 family」表で
BrunnMinkowski は **Round 2 (中-大)** 候補。verbatim 再計数 (2026-05-25):

- `Common2026/Shannon/BrunnMinkowski*.lean` 6 file の legacy marker 総計
  **40 declaration** (runbook 推定 30 と spec 推定 46 の中間、`@audit:suspect` 中心)。
- 内訳 (declaration-level、Bash `awk` で legacy marker → 直後 decl の対応抽出):
  - `BrunnMinkowskiFunctional.lean` — **13** (suspect 11、+ structure `IsPrekopaLeindlerHyp`
    `IsIndicatorToConvexBodyHyp` 2 件の冒頭散文 `🟢ʰ load-bearing — NOT a discharge`)
  - `BrunnMinkowskiConcavity.lean` — **11** (suspect 11、すべて `brunn-minkowski-closure-plan`)
  - `BrunnMinkowski.lean` — **5** (suspect 3 = `brunn-minkowski-moonshot-plan`、+ `IsBrunnMinkowskiEntropyHypothesis`
    `@audit:defect(circular)+@audit:defer+@audit:staged` 1 件、+ `brunn_minkowski_entropy_inequality`
    `@audit:defect(circular)+@audit:defer` 1 件、本体 `:= h_bm_entropy_assumed` で tier 5)
  - `BrunnMinkowskiClosure.lean` — **4** (suspect 2 = `brunn_minkowski_volume_indicator` / `brunn_minkowski_entropy_jointPi`、
    + `volume_smul_nDim` docstring 内散文 `🟢ʰ`、+ ファイル末尾 §J `🟢ʰ honest landing` 散文 1 件)
  - `BrunnMinkowskiPLBody.lean` — **5** (suspect 5、すべて `brunn-minkowski-closure-plan`)
  - `BrunnMinkowskiLayerCakeBody.lean` — **2** (suspect 2、すべて `brunn-minkowski-closure-plan`)
- `@audit:staged(epi-n-dim)` 1 件 (`IsBrunnMinkowskiEntropyHypothesis`、`@audit:defect(circular)` と重畳)
- `@audit:defer(brunn-minkowski-from-epi-discharge)` 2 件 (predicate + 主定理、同上重畳)
- `@audit:defect(circular)` **2 件** (`IsBrunnMinkowskiEntropyHypothesis` + `brunn_minkowski_entropy_inequality`、
  両者は仮説型 ≡ 結論型 で body `:= h_bm_entropy_assumed`、**tier 5 真の defect** が文字通り暫定マーカー
  として既に書かれている。本 sweep の **honesty 焦点はここ**)
- `@audit:suspect(prekopa-leindler-induction-plan)` 1 件 (`prekopa_leindler_inequality`)
- `@audit:suspect(brunn-minkowski-closure-plan)` 28 件
- `@audit:suspect(brunn-minkowski-moonshot-plan)` 3 件
- 既存 `sorry` 1 件 (`BrunnMinkowskiLayerCakeBody.lean` word-boundary 計数で 1 hit、本 sweep で
  `@residual` 付与漏れの可能性。**Pattern D 適用、Inventory step で verbatim 再確認必須**)
- 既存 `@residual` 0 件 (`rg '@residual' Common2026/Shannon/BrunnMinkowski*.lean` 結果)
- 既存 HONESTY ALERT / FALSE は **検出 0 件** (Pattern H 安全)

### 上位 moonshot との関係 (重要)

`brunn-minkowski-moonshot-plan.md` は **hypothesis pass-through publish 済**
(`brunn_minkowski_entropy_inequality` は `IsBrunnMinkowskiEntropyHypothesis = 結論` を仮説として
受け取り `:= h_bm_entropy_assumed` で着地 = **conclusion-as-hypothesis defect**)。本 plan は
その defect 状態を **2 段階で改善**:

1. **`BrunnMinkowski.lean` の tier 5 defect 2 件** (`IsBrunnMinkowskiEntropyHypothesis` +
   `brunn_minkowski_entropy_inequality`) を **第一選択 — 定義書換 → sorry+@residual 経由** に
   置換する。signature 改変が必要 (predicate を `Prop := True` 化または primitive structure 化、
   または predicate 自体を削除して body sorry に降ろす)。
2. **`@audit:suspect` を sorry-based に移行する** Hoeffding/Cramer/WynerZiv pilot と同じレシピを
   残り 28 件に適用。

ただし sibling plan [`brunn-minkowski-closure-plan.md`](brunn-minkowski-closure-plan.md) は
**Phase 1-4 完了** で entropy 形 BM `brunn_minkowski_entropy_inequality_genuine` (`BrunnMinkowskiClosure.lean:531`)
+ scaledMul 版 `brunn_minkowski_entropy_inequality_scaledMul` (`:695`) を **既に genuine chain で
publish 済** (suspect の load-bearing 部分は `IsUniformOnEntropyLogVol` 3 + `IsBMEntropyPowerVolumeHyp` 1
の 4 honest hyp に縮約)。**この closure plan 経路は本 sweep の touch 対象に含めない**:
本 sweep が `BrunnMinkowskiClosure.lean` の `brunn_minkowski_entropy_jointPi` (`:493`) を sorry
化すると closure plan Phase 4 の genuine chain が逆行するため。

→ 詳細は §「方向衝突」+ §「撤退ライン」L-MIG-3。

### Honesty workflow と DoD

本 plan の DoD は `CLAUDE.md`「Definition of Done — 2 段階」の **type-check done**:

- 各 file `lake env lean Common2026/Shannon/<file>.lean` が 0 errors、
- 各新規 `sorry` に `@residual(<class>:<slug>)` タグが付き、
- 各 Phase 完了時に honesty-auditor (or `general-purpose` SoT-brief) を起動して classification を独立検証。

`@audit:ok` (proof done) は **本 plan の出力にしない** — Mathlib 壁 (n-dim Prékopa-Leindler の
Fubini 配線、凸体 Brunn-Minkowski の Mathlib 不在) の closure は本 plan scope 外。

## Approach

### 全体戦略

**file 単位 sweep を 3 Phase に分割**、共有 wall lemma は **集約候補あり** (audit-tags.md
「Wall name register」拡張提案 R4 として `wall:n-dim-prekopa-leindler` + `wall:bm-convex-body-sqrt`
の 2 件追加を本 plan に同梱):

1. **Phase 1 — Cleanup pass (低 risk substitution)**:
   - パターン V / C に該当する pass-through wrapper / constructive bridge を sweep。
   - signature 改変なし、`@audit:suspect` タグ削除のみ。
   - **circular passthrough wrapper の警戒**: BrunnMinkowski 系は `IsBrunnMinkowskiEntropyHypothesis n h X Y P`
     や `IsUniformOnEntropyLogVolHypothesis` 等の load-bearing predicate hypothesis を pass-through する
     `_exp_form` / `_three_arg` / `_log_form` 系 wrapper が大量 (Concavity 11 件のほぼ全部)。
     これらは upstream の tier 5 defect (`brunn_minkowski_entropy_inequality`) に transitive 依存する
     **pattern V+P 混合**。Phase 1 では tag 削除のみ、residual は付与せず docstring 散文で transitive 性を
     明示 (Pilot Pattern C)。

2. **Phase 2 — Predicate retreat (signature 改変 + 新規 sorry)**:
   - パターン P (load-bearing predicate consumer) を sweep。
   - **`BrunnMinkowski.lean` の tier 5 defect 2 件** はここで **第一選択 (定義書換)** を試みる:
     - `IsBrunnMinkowskiEntropyHypothesis : Prop := <結論>` (predicate 自体が結論 unfold) を
       **削除**し、`brunn_minkowski_entropy_inequality` の body を **directly `sorry` + `@residual(plan:brunn-minkowski-sorry-migration-plan)`**
       に降ろす (`h_bm_entropy_assumed` 引数も削除)。
     - **ただし** Concavity / Functional 11+11 件が `IsBrunnMinkowskiEntropyHypothesis` を hypothesis として
       消費しているため、predicate を削除すると downstream signature が drift (Pattern E)。**impact mitigation**:
       predicate を削除せず `@audit:retract-candidate(load-bearing-predicate, conclusion-as-hypothesis)` を付与する
       + `brunn_minkowski_entropy_inequality` の body だけ `sorry` 化 + signature から `h_bm_entropy_assumed` 削除。
     - downstream wrapper (Concavity 11 + Functional Phase 2 の 8) は parent への引数渡しが消えた分を
       transitive sorry 受け渡しに変える (Pattern C transitive、tag 不要)。
   - 既存 `@audit:defect(circular)` / `@audit:defer(brunn-minkowski-from-epi-discharge)` / `@audit:staged(epi-n-dim)`
     の重畳 tag は signature が `sorry` 化されたら **削除** + `@residual(plan:brunn-minkowski-sorry-migration-plan)`
     1 行に統一 (audit-tags.md「Deprecated」表に従う)。
   - 28 件の `@audit:suspect(brunn-minkowski-closure-plan)` のうち **既存 closure plan で genuine 化済の declaration**
     を Phase 2 で sorry 化するのは方向衝突 (L-MIG-3)。具体的に:
     - `BrunnMinkowskiClosure.lean:373 brunn_minkowski_volume_indicator` — Phase 1 段階着地点として
       genuine 着地済、本 sweep では **触らず tag のみ migration** (`@audit:suspect` → そのまま残置 or
       `@audit:retract-candidate(closure-plan-completed)` 付与判断は Phase 2 で auditor 委任)
     - `BrunnMinkowskiClosure.lean:493 brunn_minkowski_entropy_jointPi` — Phase 3 pivot で 4 honest hyp に
       縮約済、closure plan の Phase V cleanup 待ち。本 sweep では **touch しない** (sorry 化すると closure
       plan の genuine chain を逆行する)。
   - Phase 2 で predicate `IsBrunnMinkowskiEntropyHypothesis` / `IsUniformOnEntropyLogVolHypothesis` /
     `IsMinkowskiSumMeasurableHypothesis` / `IsBMEntropyPowerVolumeHyp` 等の retract 判断は **Phase 2.3 で
     auditor 委任** (cross-file consumer の集計が必要)。

3. **Phase 3 — `IsPrekopaLeindlerHyp` / `IsIndicatorToConvexBodyHyp` の structure scope**:
   - `BrunnMinkowskiFunctional.lean:153 IsPrekopaLeindlerHyp` / `:174 IsIndicatorToConvexBodyHyp`
     は **structure** で `bound : <conclusion>` 単一フィールド (旧版 `def := conclusion` の循環を
     structure 化で type ≠ conclusion 化したと docstring が宣言)。
   - 構造的に load-bearing claim を 1 field に持つ structure は **Hoeffding pattern P と同等**。本 sweep では
     structure 自体を **`@audit:retract-candidate(load-bearing-predicate)`** マークに移行 +
     `prekopa_leindler_inequality` / `brunn_minkowski_from_prekopa_leindler` の body を `sorry` +
     `@residual(plan:brunn-minkowski-sorry-migration-plan)` 化。
   - construct 側 (`isPrekopaLeindlerHyp_of_1D_body` / `isPrekopaLeindlerHyp_of_layercake` /
     `indicatorToConvexBody_of_1D_body`) は **structure を作る側** で transitive sorry に降格。

### Phase 順序の理由

- Phase 1 → 2 → 3 の順は **影響範囲の小さい順**。Phase 1 (tag 削除のみ) で 9-12 件解消、Phase 2 で
  upstream の tier 5 defect 解消 (これが解消されると Concavity 11 件は transitive sorry に自動降格)、
  Phase 3 で structure-level の predicate retract。
- 逆順 (Phase 3 → 2 → 1) だと、Phase 3 で structure を残したまま Phase 2 で predicate を消すと、
  Concavity 側で「structure を hypothesis として受け取るが predicate は消えた」状態となり整合性が崩れる。

### Wall name register 拡張提案 (R4)

本 sweep で `wall:` class の `@residual` は **新規 2 wall を追加候補**:

1. **`wall:n-dim-prekopa-leindler`** — n-dim PL の Fubini 帰納 (Cover-Thomas Ch.17.9 induction-on-n)。
   Mathlib に **不在** (closure plan Phase 1 で `MeasurableEquiv.piFinSuccAbove` + `volume_preserving_piFinSuccAbove`
   経由で genuine 着地済だが、closure plan は `IsSlicePLReadyHyp` (slice 1D PL readiness) を honest hyp
   として残しており、その discharge は Mathlib 1D PL の不在に直結)。
   - 該当 declaration: `BrunnMinkowskiFunctional.lean:210 prekopa_leindler_inequality` (本 sweep Phase 3 で
     `@residual(wall:n-dim-prekopa-leindler)` 付与候補)
   - 該当 plan: `prekopa-leindler-induction-plan.md` (未着手、本 sweep が wall 命名を提供することで slug 整合)

2. **`wall:bm-convex-body-sqrt`** — 凸体 Brunn-Minkowski の sqrt 形 `volAB^(1/n) ≥ volA^(1/n) + volB^(1/n)`。
   Mathlib 不在 (closure plan Phase 3 pivot で `IsBMEntropyPowerVolumeHyp` honest hyp として外出し済)。
   - 該当 declaration: `BrunnMinkowskiClosure.lean:493 brunn_minkowski_entropy_jointPi` の
     `h_geom_bm_assumed : IsBMEntropyPowerVolumeHyp` (本 sweep では **touch しない** が、closure plan の
     Phase V cleanup で `@residual(wall:bm-convex-body-sqrt)` 化検討候補)

これらの wall 追加は本 plan の commit に同梱せず、**別 PR で `docs/audit/audit-tags.md` 拡張** を提案する
(audit-tags.md 「Wall name register」の運用ルール「新規追加時は本 register に PR で追記」に従う)。
本 plan の `@residual` class は **`plan:brunn-minkowski-sorry-migration-plan`** で揃え、wall 化は後続 PR に委ねる。

### 移行レシピ (declaration 単位)

`docs/audit/audit-tags.md`「移行レシピ」をそのまま適用するが、BrunnMinkowski 系では declaration ごとに
**4 つのパターン** が出現する:

- **パターン P-1 (`IsBrunnMinkowskiEntropyHypothesis` consumer)**: signature が
  `h_bm : IsBrunnMinkowskiEntropyHypothesis n h X Y P` を取り、body は `:= h_bm` または
  `unfold IsBrunnMinkowskiEntropyHypothesis at h_bm; rw [...]; exact h_bm` 等の pass-through。
  - 移行: `h_bm` hypothesis を **削除**、結論型は変えない、body `sorry` + `@residual(plan:brunn-minkowski-sorry-migration-plan)`。
  - **特例**: `BrunnMinkowski.lean:192 brunn_minkowski_entropy_inequality` 自体が tier 5 defect。signature 改変
    + body sorry 化。`@audit:defect(circular)` / `@audit:defer` / `@audit:staged` 重畳 tag は削除。

- **パターン P-2 (`IsUniformOnEntropyLogVolHypothesis` consumer)**: signature が 3 本の uniform=log-vol equality
  hypothesis を取り、body は `unfold ...; rw [hA_unif, hB_unif, hAB_unif] at ...; exact ...` で書き換える。
  - 移行: 3 本の uniform hypothesis を **削除**、結論型は変えない、body `sorry` + `@residual(plan:brunn-minkowski-sorry-migration-plan)`。
  - **regularity hyp 判定**: `hvolA : 0 < volA` 等の正値性は precondition なので残す。

- **パターン V (variational / regularity pass-through)**: signature が `h_pt : ∀ x y, ...` 等の
  pointwise PL 仮定 + `IsPL11DSuperLevelHyp` / `IsPL1LayerCakeIntegralHyp` / `IsTailIntegrableHyp` 等の
  **regularity bundle predicate** を取り、body は in-tree primitive (`pl1_additive_via_layercake` 等) を
  呼ぶだけ。
  - 移行: tag を **削除**するだけ (residual を新規に作らない、type-check done のまま)。
  - 候補 declaration: `BrunnMinkowskiLayerCakeBody.lean:183 prekopa_leindler_1D_layercake` /
    `:209 isPrekopaLeindlerHyp_of_layercake`、`BrunnMinkowskiPLBody.lean:219 prekopa_leindler_1D_body` /
    `:268 pl2_induction_scalar_combine` / `:287 prekopa_leindler_induction_step` /
    `:306 isPrekopaLeindlerHyp_of_1D_body` / `:342 indicatorToConvexBody_of_1D_body`。
  - **境界例**: `IsPL2FubiniSliceHyp` (`BrunnMinkowskiPLBody.lean:241`、scalar 等式 placeholder
    `intF = reduceF ∧ ...`) は closure plan 内で **「実 Fubini 未接続の旧 placeholder」と明示**、
    実装は `integral_pi_succ_eq` (closure plan Phase 1) に置き換え済。本 sweep では本 predicate を
    touch しない (closure plan が retract-candidate 化判断)。

- **パターン C (constructive transitive pass-through)**: Phase 2 で upstream を sorry 化すると本来
  constructive な caller が transitive sorry を引き継ぐ。例: Concavity 11 件のほぼ全部
  (`brunn_minkowski_convex_body_log_form` / `_exp_log_form` / `_rpow_form` 等は
  `brunn_minkowski_convex_body` を呼ぶだけ、後者は `BrunnMinkowski.lean:247` の P-1 + P-2 mixed 形)。
  - 移行 (Pilot Pattern C 適用): `@residual` タグを付与せず、docstring 散文で次を明示:
    ```
    Transitive `sorry` via `<upstream decl>` (sorry-migration Phase 2 retreat). No `@residual`
    tag is attached — the closure responsibility belongs to the upstream declaration's
    `@residual(plan:brunn-minkowski-sorry-migration-plan)`.
    ```

詳細な per-declaration の pattern 判定は次セクション「在庫」表で示す。

## 在庫: 40 件 declaration の verbatim 分類

verbatim 確認方法: `Common2026/Shannon/BrunnMinkowski*.lean` を Read で legacy marker 周辺
docstring + 直後 `theorem`/`def`/`structure` signature + body 1-3 行を実コードから読み込み。
本 plan 起草時 (2026-05-25) の line 番号で記録、Phase 0 で実装時に再確認 (verbatim 確認義務)。

| # | file:line | decl 名 | 現タグ | パターン | 結論型 (verbatim) | 提案 `@residual(class:slug)` | wall 集約? | cross-family? |
|---|---|---|---|---|---|---|---|---|
| 1 | `BrunnMinkowski.lean:134` | `IsBrunnMinkowskiEntropyHypothesis` (def) | `@audit:defect(circular)` + `@audit:defer(brunn-minkowski-from-epi-discharge)` + `@audit:staged(epi-n-dim)` | **tier 5 defect (circular)** | `Prop := entropyPower_nDim ... ≥ ... + ...` (= 結論 unfold) | (signature 改変 — `Prop := True` placeholder 化 + `@audit:retract-candidate(load-bearing-predicate, conclusion-as-hypothesis)` 付与、または structure 化検討) | no | yes (Concavity 11 件 + Functional 6 件 consumer) |
| 2 | `BrunnMinkowski.lean:192` | `brunn_minkowski_entropy_inequality` | `@audit:defect(circular)` + `@audit:defer(brunn-minkowski-from-epi-discharge)` | **tier 5 defect (circular)** | `entropyPower_nDim n h (P.map (X+Y)) ≥ ... + ...` (body `:= h_bm_entropy_assumed`) | `plan:brunn-minkowski-sorry-migration-plan` (signature から `h_bm` 削除、body sorry) | no | no |
| 3 | `BrunnMinkowski.lean:209` | `brunn_minkowski_entropy_inequality_exp_form` | `@audit:suspect(brunn-minkowski-moonshot-plan)` | P-1 (`IsBrunnMinkowskiEntropyHypothesis` consumer) | `Real.exp ((2/n) * h (P.map (X+Y))) ≥ ...` | `plan:brunn-minkowski-sorry-migration-plan` | no | no |
| 4 | `BrunnMinkowski.lean:247` | `brunn_minkowski_convex_body` | `@audit:suspect(brunn-minkowski-moonshot-plan)` | P-2 (3 `IsUniformOnEntropyLogVolHypothesis` + 1 `IsMinkowskiSumMeasurableHypothesis` + sharp form hyp) | `Real.exp ((1/n) * Real.log volAB) ≥ ...` | `plan:brunn-minkowski-sorry-migration-plan` | (`wall:bm-convex-body-sqrt` 候補だが R4 拡張で別 PR) | no |
| 5 | `BrunnMinkowski.lean:293` | `brunn_minkowski_entropy_inequality_three_arg` | `@audit:suspect(brunn-minkowski-moonshot-plan)` | P-1 (2 件の `IsBrunnMinkowskiEntropyHypothesis`) | `entropyPower_nDim n h (P.map (X+Y+Z)) ≥ ... + ... + ...` | `plan:brunn-minkowski-sorry-migration-plan` | no | no |
| 6 | `BrunnMinkowskiFunctional.lean:153` | `IsPrekopaLeindlerHyp` (structure) | 散文 `🟢ʰ load-bearing — NOT a discharge` | **tier 4 → P (structure with `bound` field)** | `bound : intF ^ lam * intG ^ (1 - lam) ≤ intH` | (structure に `@audit:retract-candidate(load-bearing-predicate)` 付与、Phase 3) | yes (`wall:n-dim-prekopa-leindler` R4 候補) | yes (`BrunnMinkowskiPLBody.lean:306` constructor + `:317` 同上 + Concavity / Functional consumer) |
| 7 | `BrunnMinkowskiFunctional.lean:174` | `IsIndicatorToConvexBodyHyp` (structure) | 散文 `🟢ʰ load-bearing — NOT a discharge` | **tier 4 → P (structure with `bound` field)** | `bound : volA ^ lam * volB ^ (1 - lam) ≤ volAB` | (structure に `@audit:retract-candidate(load-bearing-predicate)` 付与、Phase 3) | yes (`wall:bm-convex-body-sqrt` R4 候補) | yes (`BrunnMinkowskiPLBody.lean:342` constructor + Functional `:239`, `:482` consumer) |
| 8 | `BrunnMinkowskiFunctional.lean:210` | `prekopa_leindler_inequality` | 散文 `🟢ʰ load-bearing` + `@audit:suspect(prekopa-leindler-induction-plan)` | P (structure `IsPrekopaLeindlerHyp` consumer) | `intF ^ lam * intG ^ (1 - lam) ≤ intH` | `plan:brunn-minkowski-sorry-migration-plan` (or 別 PR `wall:n-dim-prekopa-leindler` 後追加) | yes (R4 候補) | no |
| 9 | `BrunnMinkowskiFunctional.lean:239` | `brunn_minkowski_from_prekopa_leindler` | 散文 `🟢ʰ load-bearing` + `@audit:suspect(brunn-minkowski-closure-plan)` | P (structure `IsIndicatorToConvexBodyHyp` consumer) | `volA ^ lam * volB ^ (1 - lam) ≤ volAB` | `plan:brunn-minkowski-sorry-migration-plan` | yes (R4 候補) | no |
| 10 | `BrunnMinkowskiFunctional.lean:299` | `entropyPower_nDim_le_volume_rpow_of_logConcave` | `@audit:suspect(brunn-minkowski-closure-plan)` | V+P (log-concave + `h_le_logVol_hyp : h μ ≤ Real.log volA`) | `entropyPower_nDim n h μ ≤ volA ^ ((2 : ℝ) / n)` | `plan:brunn-minkowski-sorry-migration-plan` | no | no |
| 11 | `BrunnMinkowskiFunctional.lean:432` | `entropy_power_lambda_mixing` | `@audit:suspect(brunn-minkowski-closure-plan)` | P-1 (`h_pl_entropy : ... ≤ ...` = 結論そのものを hypothesis) **境界 tier 5 circular** | `entropyPower_nDim n h (P.map X)^lam * ...^(1-lam) ≤ entropyPower_nDim n h (P.map (lam•X+(1-lam)•Y))` | `plan:brunn-minkowski-sorry-migration-plan` (body `:= h_pl_entropy` is circular — Phase 2 で sorry 化 + `@residual(defect:circular)` も検討) | no | no |
| 12 | `BrunnMinkowskiFunctional.lean:458` | `entropy_concave_lambda_mixing` | `@audit:suspect(brunn-minkowski-closure-plan)` | **境界 tier 5 circular** (`h_concave_hyp` = 結論そのもの、body `:= h_concave_hyp`) | `lam * h (P.map X) + (1-lam) * h (P.map Y) ≤ h (P.map (lam•X+(1-lam)•Y))` | `plan:brunn-minkowski-sorry-migration-plan` (Phase 2、`@residual(defect:circular)` 検討) | no | no |
| 13 | `BrunnMinkowskiFunctional.lean:482` | `prekopa_leindler_geometric_mean_form` | `@audit:suspect(brunn-minkowski-closure-plan)` | P (structure `IsIndicatorToConvexBodyHyp` λ=1/2 specialize) | `volA^(1/2) * volB^(1/2) ≤ volAB` | `plan:brunn-minkowski-sorry-migration-plan` | no | no |
| 14 | `BrunnMinkowskiFunctional.lean:503` | `brunn_minkowski_linear_from_prekopa_leindler` | `@audit:suspect(brunn-minkowski-closure-plan)` | **境界 tier 5 circular** (`h_linear_hyp : volA+volB ≤ volAB`、body `:= h_linear_hyp`) | `volA + volB ≤ volAB` | `plan:brunn-minkowski-sorry-migration-plan` (Phase 2、`@residual(defect:circular)` 検討) | no | no |
| 15 | `BrunnMinkowskiFunctional.lean:523` | `entropyPower_nDim_logConcave_brunn_minkowski` | `@audit:suspect(brunn-minkowski-closure-plan)` | P-1 (`IsBrunnMinkowskiEntropyHypothesis` consumer) | `entropyPower_nDim n h (P.map (X+Y)) ≥ ...` | `plan:brunn-minkowski-sorry-migration-plan` | no | no |
| 16 | `BrunnMinkowskiFunctional.lean:540` | `brunn_minkowski_convex_body_logConcave` | `@audit:suspect(brunn-minkowski-closure-plan)` | P-1 + P-2 mixed (`h_lc_X/Y` + 3 uniform + sharp form hyp) | `Real.exp ((1/n) * Real.log volAB) ≥ ...` | `plan:brunn-minkowski-sorry-migration-plan` | no | no |
| 17 | `BrunnMinkowskiFunctional.lean:586` | `entropy_eq_logVolume_iff_uniform` | `@audit:suspect(brunn-minkowski-closure-plan)` | **境界 tier 5 circular** (`h_eq_hyp : h μ = Real.log vol`、body `:= h_eq_hyp`) | `h μ = Real.log vol` | `plan:brunn-minkowski-sorry-migration-plan` (Phase 2、`@residual(defect:circular)` 検討) | no | no |
| 18 | `BrunnMinkowskiFunctional.lean:627` | `coverThomas17_9_bundle_entropy` | `@audit:suspect(brunn-minkowski-closure-plan)` | P-1 (bundle structure consumer + `IsBrunnMinkowskiEntropyHypothesis` 経由) | `entropyPower_nDim n h (P.map (X+Y)) ≥ ... + ...` | `plan:brunn-minkowski-sorry-migration-plan` (transitive、bundle structure 自体 retract 検討) | no | yes (`CoverThomas17_9_Bundle` structure を consume) |
| 19 | `BrunnMinkowskiConcavity.lean:214` | `brunn_minkowski_convex_body_log_form` | `@audit:suspect(brunn-minkowski-closure-plan)` | C transitive (`brunn_minkowski_convex_body` 呼出) | `(1/n) * Real.log volAB ≥ Real.log (Real.exp(...)+Real.exp(...))` | (タグ削除のみ — transitive) | no | no |
| 20 | `BrunnMinkowskiConcavity.lean:244` | `brunn_minkowski_convex_body_exp_log_form` | `@audit:suspect(brunn-minkowski-closure-plan)` | C transitive | `Real.exp((1/n)*Real.log volAB) ≥ Real.exp(...)+Real.exp(...)` | (タグ削除のみ) | no | no |
| 21 | `BrunnMinkowskiConcavity.lean:276` | `brunn_minkowski_entropy_log_form` | `@audit:suspect(brunn-minkowski-closure-plan)` | C transitive (P-1 経由 `brunn_minkowski_entropy_inequality_exp_form`) | `(2/n) * h (P.map (X+Y)) ≥ Real.log (...)` | (タグ削除のみ) | no | no |
| 22 | `BrunnMinkowskiConcavity.lean:432` | `brunn_minkowski_concavity_of_log_wrapper` | `@audit:suspect(brunn-minkowski-closure-plan)` | C transitive (`brunn_minkowski_entropy_log_form` 呼出) | 同 21 | (タグ削除のみ) | no | no |
| 23 | `BrunnMinkowskiConcavity.lean:449` | `brunn_minkowski_concavity_max_lower_bound` | `@audit:suspect(brunn-minkowski-closure-plan)` | C transitive | `(2/n) * h (P.map (X+Y)) ≥ max ...` | (タグ削除のみ) | no | no |
| 24 | `BrunnMinkowskiConcavity.lean:467` | `brunn_minkowski_concavity_max_log_two_upper_bound` | `@audit:suspect(brunn-minkowski-closure-plan)` | C transitive | conjunction | (タグ削除のみ) | no | no |
| 25 | `BrunnMinkowskiConcavity.lean:569` | `brunn_minkowski_entropy_ge_one_side` | `@audit:suspect(brunn-minkowski-closure-plan)` | C transitive (`brunn_minkowski_entropy_inequality` + `nonneg` で `linarith`) | `entropyPower_nDim n h (P.map (X+Y)) ≥ entropyPower_nDim n h (P.map X)` | (タグ削除のみ — transitive) | no | no |
| 26 | `BrunnMinkowskiConcavity.lean:586` | `brunn_minkowski_entropy_ge_other_side` | `@audit:suspect(brunn-minkowski-closure-plan)` | C transitive | mirror | (タグ削除のみ) | no | no |
| 27 | `BrunnMinkowskiConcavity.lean:605` | `brunn_minkowski_entropy_ge_max` | `@audit:suspect(brunn-minkowski-closure-plan)` | C transitive (上 2 件 `max_le`) | `... ≥ max ...` | (タグ削除のみ) | no | no |
| 28 | `BrunnMinkowskiConcavity.lean:625` | `brunn_minkowski_convex_body_rpow_form` | `@audit:suspect(brunn-minkowski-closure-plan)` | C transitive (`brunn_minkowski_convex_body` 呼出 + `exp_inv_n_log_eq_rpow`) | `volAB^(1/n) ≥ volA^(1/n) + volB^(1/n)` | (タグ削除のみ) | (`wall:bm-convex-body-sqrt` の結論型と一致、R4 候補) | no |
| 29 | `BrunnMinkowskiConcavity.lean:656` | `brunn_minkowski_convex_body_rpow_pos` | `@audit:suspect(brunn-minkowski-closure-plan)` | C transitive | mirror with `0 < volA` etc. | (タグ削除のみ) | no | no |
| 30 | `BrunnMinkowskiClosure.lean:373` | `brunn_minkowski_volume_indicator` | `@audit:suspect(brunn-minkowski-closure-plan)` | V (closure plan §F 段階着地点、`h_pl : ... ≤ ...` PL 結論を hypothesis として直接受領) | `(volume A).toReal ^ lam * (volume B).toReal ^ (1-lam) ≤ (volume (lam•A+(1-lam)•B)).toReal` | **本 sweep では touch しない** (closure plan 完了済の genuine 着地点) — タグは `@audit:retract-candidate(closure-plan-completed)` 化を Phase 2 で auditor 委任 | no | yes (closure plan 領域) |
| 31 | `BrunnMinkowskiClosure.lean:426` | `volume_smul_nDim` (docstring 内散文 `🟢ʰ`) | 散文 `🟢ʰ honest 副条件付き` (docstring 内、§G 設計判断記述) | (genuine、tag 不在) | `volume (r • A) = ENNReal.ofReal (r ^ n) * volume A` | (散文 `🟢ʰ` を削除するだけ、Phase 1 cleanup) | no | no |
| 32 | `BrunnMinkowskiClosure.lean:493` | `brunn_minkowski_entropy_jointPi` | 散文 `🟢ʰ load-bearing — NOT a discharge` + `@audit:suspect(brunn-minkowski-closure-plan)` | **closure plan Phase 3 pivot で 4 honest hyp 縮約済** (`hA_unif/hB_unif/hAB_unif` + `IsBMEntropyPowerVolumeHyp`) | `entropyPower_nDim n hJoint (P.map (X+Y)) ≥ ... + ...` | **本 sweep では touch しない** (closure plan が `wall:bm-convex-body-sqrt` 化検討中) — タグは `@audit:retract-candidate(closure-plan-completed)` 化を Phase 2 で auditor 委任 | no | yes (closure plan 領域) |
| 33 | `BrunnMinkowskiClosure.lean:881` | `measurable_cons_left` 周辺 §J docstring 内散文 | 散文 `BM は 🟢ʰ が honest landing` (docstring 内、§J 設計判断記述) | (genuine、tag 不在) | (declaration 自体は `Measurable (fun w => Fin.cons s w)` genuine) | (散文 `🟢ʰ` を削除するだけ、Phase 1 cleanup) | no | no |
| 34 | `BrunnMinkowskiPLBody.lean:219` | `prekopa_leindler_1D_body` | `@audit:suspect(brunn-minkowski-closure-plan)` | V (regularity bundle `IsPL11DSuperLevelHyp` + `IsPL1AdditiveHyp` + pointwise PL) | `intF ^ lam * intG ^ (1 - lam) ≤ intH` (body: weighted_amgm + linarith) | (タグ削除のみ — Phase 1) | (`IsPL1AdditiveHyp` は load-bearing claim を bundle するため境界例 — auditor 委任) | no |
| 35 | `BrunnMinkowskiPLBody.lean:268` | `pl2_induction_scalar_combine` | `@audit:suspect(brunn-minkowski-closure-plan)` | V (Fubini scalar equality bundle `IsPL2FubiniSliceHyp` + slice PL conclusion) | `intF ^ lam * intG ^ (1 - lam) ≤ intH` | (タグ削除のみ — Phase 1) | no | no |
| 36 | `BrunnMinkowskiPLBody.lean:287` | `prekopa_leindler_induction_step` | `@audit:suspect(brunn-minkowski-closure-plan)` | V transitive (上の `pl2_induction_scalar_combine` 経由) | 同 35 | (タグ削除のみ — Phase 1) | no | no |
| 37 | `BrunnMinkowskiPLBody.lean:306` | `isPrekopaLeindlerHyp_of_1D_body` | `@audit:suspect(brunn-minkowski-closure-plan)` | C (structure constructor、`prekopa_leindler_1D_body` 経由) | `IsPrekopaLeindlerHyp f g hfn lam intF intG intH` | (タグ削除のみ — Phase 1、ただし Phase 3 で structure が retract された場合は transitive 化) | no | yes (`IsPrekopaLeindlerHyp` constructor) |
| 38 | `BrunnMinkowskiPLBody.lean:342` | `indicatorToConvexBody_of_1D_body` | `@audit:suspect(brunn-minkowski-closure-plan)` | C (structure constructor、`bm_additive_to_multiplicative` 経由) | `IsIndicatorToConvexBodyHyp A B volA volB volAB lam` | (タグ削除のみ — Phase 1、Phase 3 で structure retract 時は transitive 化) | no | yes (`IsIndicatorToConvexBodyHyp` constructor) |
| 39 | `BrunnMinkowskiLayerCakeBody.lean:183` | `prekopa_leindler_1D_layercake` | `@audit:suspect(brunn-minkowski-closure-plan)` | V (regularity bundle `IsPL11DSuperLevelHyp` + `IsPL1LayerCakeIntegralHyp` + `IsTailIntegrableHyp` + pointwise PL) | `intF ^ lam * intG ^ (1 - lam) ≤ intH` | (タグ削除のみ — Phase 1) | no | no |
| 40 | `BrunnMinkowskiLayerCakeBody.lean:209` | `isPrekopaLeindlerHyp_of_layercake` | `@audit:suspect(brunn-minkowski-closure-plan)` | C (structure constructor、上の `prekopa_leindler_1D_layercake` 経由) | `IsPrekopaLeindlerHyp f g hfn lam intF intG intH` | (タグ削除のみ — Phase 1) | no | yes (`IsPrekopaLeindlerHyp` constructor) |

### 集計 (パターン別)

- **tier 5 defect (circular)**: **2 件** (Phase 2、`BrunnMinkowski.lean:134` + `:192`)
- **境界 tier 5 (circular suspect の中に紛れる)**: **4 件**
  (`BrunnMinkowskiFunctional.lean:432, :458, :503, :586` — body が `:= h_xxx` で結論型 ≡ 仮説型)
- **P-1 / P-2 (predicate consumer、signature 改変 + sorry)**: **9 件**
  (`BrunnMinkowski.lean:209, :247, :293`、`BrunnMinkowskiFunctional.lean:210, :239, :299, :482, :523, :540, :627`)
- **V (variational / regularity bundle pass-through)**: **6 件**
  (`BrunnMinkowskiPLBody.lean:219, :268, :287`、`BrunnMinkowskiLayerCakeBody.lean:183`、`BrunnMinkowskiClosure.lean:426 docstring`、`:881 docstring`)
- **C transitive**: **13 件**
  (Concavity 11 件すべて + `BrunnMinkowskiPLBody.lean:306, :342` + `BrunnMinkowskiLayerCakeBody.lean:209`)
- **structure (retract-candidate)**: **2 件**
  (`BrunnMinkowskiFunctional.lean:153 IsPrekopaLeindlerHyp` + `:174 IsIndicatorToConvexBodyHyp`)
- **closure plan 完了済 (touch しない)**: **2 件**
  (`BrunnMinkowskiClosure.lean:373 brunn_minkowski_volume_indicator` + `:493 brunn_minkowski_entropy_jointPi`)
- **Cross-family / cross-file consumer 多数**:
  `IsBrunnMinkowskiEntropyHypothesis` (Concavity 11 + Functional 6 consumer)、
  `IsPrekopaLeindlerHyp` structure (PLBody 2 constructor + LayerCake 1 constructor + Functional 2 consumer)、
  `IsIndicatorToConvexBodyHyp` structure (PLBody 1 constructor + Functional 2 consumer)、
  `IsBMEntropyPowerVolumeHyp` (Closure 内のみ、closure plan 領域)。

→ **Phase 1 で 7 件処理** (V のうち 2 件 docstring 散文 `🟢ʰ` 削除 + V remaining 4 件 tag 削除 + closure plan
領域 2 件は retract-candidate 化判断 = 計 8、但し V 4 + retract 2 + docstring 2 で内訳調整)、
**Phase 2 で 15 件処理** (tier 5 defect 2 + 境界 tier 5 4 + P-1/P-2 9)、
**Phase 3 で 16 件処理** (structure retract 2 + C transitive 13 + その他 1)。
合計 40 件。

## Phase 詳細

### Phase 1 — Cleanup pass + 散文 `🟢ʰ` 除去 (低 risk、新規 sorry なし) 📋

`proof-log: no` (mechanical tag removal、Pilot Pattern と同一)。

- [ ] **1.1** `BrunnMinkowskiPLBody.lean` Phase 1 候補 5 件
  (`prekopa_leindler_1D_body` / `pl2_induction_scalar_combine` / `prekopa_leindler_induction_step` /
  `isPrekopaLeindlerHyp_of_1D_body` / `indicatorToConvexBody_of_1D_body`) の `@audit:suspect` 削除。
  - signature 改変なし、regularity hyp + structure constructor として保持。
  - `lake env lean Common2026/Shannon/BrunnMinkowskiPLBody.lean` で type-check done 確認。
  - **inline detection**: `IsPL2FubiniSliceHyp` (scalar 等式 placeholder) の load-bearing 判定は
    auditor 委任。closure plan 内で「実 Fubini 未接続の旧 placeholder」と明示済のため本 sweep では touch しない。
- [ ] **1.2** `BrunnMinkowskiLayerCakeBody.lean` Phase 1 候補 2 件
  (`prekopa_leindler_1D_layercake` / `isPrekopaLeindlerHyp_of_layercake`) の `@audit:suspect` 削除。
  - `IsPL11DSuperLevelHyp` / `IsPL1LayerCakeIntegralHyp` / `IsTailIntegrableHyp` 3 本は **regularity bundle**
    (measurability / integrability + layer-cake 等式) で load-bearing claim を bundle するものではない判定。
  - 既存 `sorry` 1 件は **verbatim 確認 + 該当行に `@residual(plan:brunn-minkowski-sorry-migration-plan)`
    付与** (Pattern D 適用、`rg -nw 'sorry'` で hit した 1 件が実 sorry か docstring 文字列かを判別)。
- [ ] **1.3** `BrunnMinkowskiClosure.lean` 散文 `🟢ʰ` 除去 2 件
  (`:426 volume_smul_nDim` docstring + `:881 measurable_cons_left` 周辺 §J docstring)。
  - declaration 自体は genuine、散文 `🟢ʰ` 表記を tier 4 deprecated 表記から 散文削除のみで処理。
  - signature / body には触らない。
- [ ] **1.4** Concavity 11 件 (`brunn_minkowski_convex_body_log_form` 〜 `_rpow_pos`) は
  **すべて transitive Pattern C** ゆえ Phase 1 ではなく Phase 3 で扱う (Phase 2 で upstream が sorry 化
  された後の transitive 整合確認が必要)。
- [ ] **1.5** Phase 1 完了時 honesty-auditor 起動。対象: 上記 7-9 件すべての declaration。verdict 確認後 commit。
  - **judge focus**: `IsPL11DSuperLevelHyp` / `IsPL1LayerCakeIntegralHyp` / `IsTailIntegrableHyp` /
    `IsPL2FubiniSliceHyp` が regularity bundle か load-bearing claim bundle か。

**Phase 1 DoD**: 9 件 (PLBody 5 + LayerCake 2 + Closure 散文 2) で `@audit:suspect` / 散文 `🟢ʰ`
が 0 件、新規 `sorry` 0 件 (LayerCake 既存 1 件は `@residual` 付与で is-tag 化、新規ではない)、
`lake env lean` 各 file 0 errors。

### Phase 2 — Predicate / tier 5 defect retreat (signature 改変 + 新規 sorry) 📋

`proof-log: yes` (`docs/shannon/proof-log-brunn-minkowski-sorry-migration-phase2.md`)。理由: signature 改変
+ tier 5 defect の sorry 化 + 4 件の境界 tier 5 (`:= h_xxx` 循環) の判定境界がある。

- [ ] **2.1** `BrunnMinkowski.lean` tier 5 defect 2 件 (`IsBrunnMinkowskiEntropyHypothesis` def +
  `brunn_minkowski_entropy_inequality` theorem) を処理。
  - **第一選択 (定義書換) を試みる**:
    - `IsBrunnMinkowskiEntropyHypothesis` の `def := <conclusion>` (line 137-138) は **predicate 自体を削除**
      しない (Concavity 11 + Functional 6 consumer が referencing するため、削除すると signature drift)。
      代わりに predicate に `@audit:retract-candidate(load-bearing-predicate, conclusion-as-hypothesis)`
      を docstring 末尾に付与 (Pilot Pattern E、retract-candidate の reason variant が拡張候補だが現状の
      `load-bearing-predicate` で代用)。
    - `brunn_minkowski_entropy_inequality` の body `:= h_bm_entropy_assumed` (line 201) は
      signature から `h_bm_entropy_assumed` を **削除**、body を `sorry` 化、tag を
      `@residual(plan:brunn-minkowski-sorry-migration-plan)` に置換。
    - 既存 `@audit:defect(circular)` / `@audit:defer(brunn-minkowski-from-epi-discharge)` / `@audit:staged(epi-n-dim)`
      の重畳 tag は **削除** (`@residual` 1 行に統一、`audit-tags.md`「Deprecated」表に従う)。
  - **第二選択 fallback**: signature drift が広範になりすぎる場合 (Concavity / Functional consumer の
    body にも変更が必要な場合)、第一選択を諦め signature を保持 + `@audit:defect(circular)` を残す
    + `@audit:closed-by-successor(brunn-minkowski-sorry-migration-plan)` 付与 (CLAUDE.md「sorry を書けない
    箇所での対処順序」第二選択)。

- [ ] **2.2** `BrunnMinkowski.lean` P-1 / P-2 系 3 件
  (`brunn_minkowski_entropy_inequality_exp_form` / `brunn_minkowski_convex_body` / `brunn_minkowski_entropy_inequality_three_arg`)。
  - signature 改変: `IsBrunnMinkowskiEntropyHypothesis` / `IsUniformOnEntropyLogVolHypothesis` /
    `IsMinkowskiSumMeasurableHypothesis` を hypothesis として持つものは **削除**。
  - `brunn_minkowski_convex_body` の `h_bm_sharp : Real.exp (...) ≥ ...` は **境界例**: conclusion-as-hypothesis
    で tier 5 候補 (auditor 委任)。
  - body `sorry` + `@residual(plan:brunn-minkowski-sorry-migration-plan)`。

- [ ] **2.3** `BrunnMinkowskiFunctional.lean` P-1 / P-2 系 6 件
  (`entropyPower_nDim_le_volume_rpow_of_logConcave` / `entropy_power_lambda_mixing` / `entropy_concave_lambda_mixing` /
  `prekopa_leindler_geometric_mean_form` / `brunn_minkowski_linear_from_prekopa_leindler` / `entropyPower_nDim_logConcave_brunn_minkowski` /
  `brunn_minkowski_convex_body_logConcave` / `entropy_eq_logVolume_iff_uniform` / `coverThomas17_9_bundle_entropy`)。
  - **境界 tier 5 4 件** (`:432, :458, :503, :586`) の inline 判定: body `:= h_xxx` 循環ゆえ
    `@residual(defect:circular)` 候補。**implementer 段階で signature を verbatim 読み確定**
    (Pilot Pattern F)。確定時は `@audit:defect(circular)` 既存 tag を `@residual(defect:circular)` に
    書換 + signature 改変 + body sorry 化。
  - **第一選択 (定義書換)** を試みる: `entropy_eq_logVolume_iff_uniform` は `Prop := h μ = Real.log vol`
    を hypothesis として受けて結論で返すだけの循環。これは **predicate 自体を削除** + body sorry の
    純循環 break が可能。
  - body `sorry` + `@residual(plan:brunn-minkowski-sorry-migration-plan)` (or `@residual(defect:circular)`)。

- [ ] **2.4** predicate 定義側の処理 (`IsBrunnMinkowskiEntropyHypothesis` /
  `IsUniformOnEntropyLogVolHypothesis` / `IsMinkowskiSumMeasurableHypothesis` / `IsBMEntropyPowerVolumeHyp`):
  - Phase 2.1-2.3 完了後、consumer 集計 (`rg -n 'IsBrunnMinkowskiEntropyHypothesis|IsUniformOnEntropyLogVolHypothesis|IsMinkowskiSumMeasurableHypothesis' Common2026/`)。
  - **closure plan 領域** (`BrunnMinkowskiClosure.lean`) は除外。
  - **依存ゼロなら**: `@audit:retract-candidate(load-bearing-predicate)` を docstring 末尾に付与。
  - **依然依存ありなら**: 「未決事項」#1 → user 判断仰ぐ。
  - **`IsBMEntropyPowerVolumeHyp`** (Closure 内、closure plan 領域) は本 sweep では **touch しない**
    (closure plan Phase V cleanup で `wall:bm-convex-body-sqrt` 化検討予定)。

- [ ] **2.5** Phase 2 完了時 honesty-auditor 起動。対象: 15 件すべての declaration + 4 件の predicate /
  structure 定義。verdict 確認後 commit。
  - **judge focus**: (a) tier 5 defect 2 件の signature が genuine 形に保たれているか、(b) 境界 tier 5
    4 件の inline 判定 (`@residual(defect:circular)` vs `@residual(plan:...)`)、(c) `brunn_minkowski_convex_body`
    の `h_bm_sharp` 境界例の判定、(d) predicate retract 整合性。

**Phase 2 DoD**:
- 15 件で `@audit:suspect` / `@audit:defect(circular)` / `@audit:defer` / `@audit:staged` 0 件、
  `@residual(plan:brunn-minkowski-sorry-migration-plan)` または `@residual(defect:circular)` 付き
  `sorry` 12-15 件 (境界 tier 5 4 件の判定次第)。
- predicate `IsBrunnMinkowskiEntropyHypothesis` / `IsUniformOnEntropyLogVolHypothesis` /
  `IsMinkowskiSumMeasurableHypothesis` は `@audit:retract-candidate(load-bearing-predicate)` 付与。
- `lake env lean` 各 file 0 errors、`Common2026.lean` の import 行は変更なし。
- olean refresh (`lake build Common2026.Shannon.BrunnMinkowski`) を Phase 2.1 完了直後に実行
  (`BrunnMinkowski.lean` signature 改変が広範な dependent (Concavity / Functional / Closure) に
  影響するため、Pilot Pattern A 適用)。

### Phase 3 — Structure retract + Concavity transitive sorry handling 📋

`proof-log: yes` (structure 操作 + transitive sorry の docstring 散文管理 + 13 件 Concavity の
mechanical な tag 整理が一気に走るため)。

- [ ] **3.1** `BrunnMinkowskiFunctional.lean` structure 2 件
  (`IsPrekopaLeindlerHyp` `:153` + `IsIndicatorToConvexBodyHyp` `:174`) の処理。
  - **第一選択 (定義書換)**: structure は `bound : <conclusion>` 単一フィールドで、Hoeffding pattern P
    と同等の load-bearing。**signature 改変**: structure を `def := True` placeholder にせず、
    そのまま保持 + `@audit:retract-candidate(load-bearing-predicate)` を docstring 末尾に付与。
  - 既存 `🟢ʰ load-bearing — NOT a discharge` 散文は **削除** (`@audit:retract-candidate` で代替)。
  - structure を consume する 8 件 (Functional `:210 prekopa_leindler_inequality`,
    `:239 brunn_minkowski_from_prekopa_leindler`, `:482 prekopa_leindler_geometric_mean_form` —
    これらは Phase 2.3 で処理済) は **structure 自体は touch しない、Phase 2 で hypothesis として
    削除済**。
  - structure constructor 3 件
    (`BrunnMinkowskiPLBody.lean:306 isPrekopaLeindlerHyp_of_1D_body` + `:342 indicatorToConvexBody_of_1D_body` +
    `BrunnMinkowskiLayerCakeBody.lean:209 isPrekopaLeindlerHyp_of_layercake`) は Phase 1 で
    `@audit:suspect` 削除済、Phase 3 では **docstring 散文に「`@audit:retract-candidate` 付与済の
    `IsPrekopaLeindlerHyp` structure を構築している」と transitive 性を明示する 1 行追加**。

- [ ] **3.2** `BrunnMinkowskiConcavity.lean` Pattern C transitive 11 件
  (`brunn_minkowski_convex_body_log_form` 〜 `_rpow_pos`) の処理。
  - **すべて `@audit:suspect(brunn-minkowski-closure-plan)` 削除**、`@residual` タグは **付与しない**
    (Pilot Pattern C transitive 適用)。
  - 各 declaration の docstring 末尾に次の散文を追加:
    ```
    Transitive `sorry` via `<upstream decl>` (sorry-migration Phase 2 retreat). No `@residual` tag
    attached — the closure responsibility belongs to the upstream declaration's
    `@residual(plan:brunn-minkowski-sorry-migration-plan)`.
    ```
  - upstream 列挙:
    - `:214 brunn_minkowski_convex_body_log_form` → upstream `brunn_minkowski_convex_body` (`BrunnMinkowski.lean:247`)
    - `:244 brunn_minkowski_convex_body_exp_log_form` → 同上
    - `:276 brunn_minkowski_entropy_log_form` → upstream `brunn_minkowski_entropy_inequality_exp_form` (`BrunnMinkowski.lean:209`)
    - `:432 brunn_minkowski_concavity_of_log_wrapper` → 同上
    - `:449 brunn_minkowski_concavity_max_lower_bound` → 同上
    - `:467 brunn_minkowski_concavity_max_log_two_upper_bound` → 同上
    - `:569 brunn_minkowski_entropy_ge_one_side` → upstream `brunn_minkowski_entropy_inequality` (`BrunnMinkowski.lean:192`)
    - `:586 brunn_minkowski_entropy_ge_other_side` → 同上
    - `:605 brunn_minkowski_entropy_ge_max` → 同上 2 件
    - `:625 brunn_minkowski_convex_body_rpow_form` → upstream `brunn_minkowski_convex_body` (`BrunnMinkowski.lean:247`)
    - `:656 brunn_minkowski_convex_body_rpow_pos` → 同上

- [ ] **3.3** `BrunnMinkowskiClosure.lean` `@audit:suspect` 2 件
  (`:373 brunn_minkowski_volume_indicator` + `:493 brunn_minkowski_entropy_jointPi`) の処理。
  - **本 sweep では body / signature を touch しない** (closure plan で genuine 着地 / 4 honest hyp 縮約済)。
  - tag は **Phase 2.5 auditor verdict 次第**: `@audit:retract-candidate(closure-plan-completed)` 付与か、
    `@audit:suspect` を保持して closure plan Phase V cleanup に委ねるか。本 plan のデフォルトは前者。
  - `:493` の散文 `🟢ʰ load-bearing — NOT a discharge` は削除し、`@audit:retract-candidate` で代替。

- [ ] **3.4** Phase 3 完了時 honesty-auditor 起動。対象: 13 件 Concavity + 2 件 structure +
  2 件 Closure tag 整理 + 3 件 structure constructor 散文追加。verdict 確認後 commit。
  - **judge focus**: (a) structure の `@audit:retract-candidate` 付与状態、(b) transitive sorry の
    docstring 散文の整合性、(c) closure plan 領域 2 件の tag 状態 (auditor 委任)。

**Phase 3 DoD**:
- 13 件 Concavity で `@audit:suspect` 0 件、`@residual` タグ 0 件 (transitive のため)、各 docstring に
  upstream 言及 1 行追加。
- 2 件 structure に `@audit:retract-candidate(load-bearing-predicate)` 付与、散文 `🟢ʰ` 削除。
- 2 件 Closure suspect tag は `@audit:retract-candidate(closure-plan-completed)` 化または現状維持。
- `lake env lean` 各 file 0 errors (transitive sorry が型システム経由で伝播するため、各 declaration の
  body は変えていないが Phase 2 の upstream signature 改変で olean refresh が必要)。

### Phase V — verify + plan の集約 + Wall name register R4 提案 📋

`proof-log: no`。

- [ ] **V.1** 全 6 file で `lake env lean` 確認 (Phase 2-3 で signature 改変 + olean refresh が必要)。
  - **olean refresh 順** (依存方向、Pilot Pattern A):
    1. `lake build Common2026.Shannon.BrunnMinkowski` (Phase 2.1 改変、Concavity / Functional / Closure が
       transitive 依存)
    2. `lake build Common2026.Shannon.BrunnMinkowskiFunctional` (Phase 2.3 改変、PLBody / Concavity が依存)
    3. `lake env lean Common2026/Shannon/BrunnMinkowskiConcavity.lean`
    4. `lake env lean Common2026/Shannon/BrunnMinkowskiPLBody.lean`
    5. `lake env lean Common2026/Shannon/BrunnMinkowskiLayerCakeBody.lean`
    6. `lake env lean Common2026/Shannon/BrunnMinkowskiClosure.lean`
- [ ] **V.2** 集計コマンド実行:
  ```bash
  rg '@audit:suspect' Common2026/Shannon/BrunnMinkowski*.lean | wc -l      # = 0 (closure plan suspect 残置を除く)
  rg '@audit:defect|@audit:defer|@audit:staged' Common2026/Shannon/BrunnMinkowski*.lean  # = closure plan 領域のみ
  rg '@residual\(plan:brunn-minkowski-sorry-migration-plan\)' Common2026/Shannon/BrunnMinkowski*.lean | wc -l
  rg '@residual\(defect:circular\)' Common2026/Shannon/BrunnMinkowski*.lean | wc -l
  rg '@audit:retract-candidate\(load-bearing-predicate' Common2026/Shannon/BrunnMinkowski*.lean | wc -l
  rg '@audit:retract-candidate\(closure-plan-completed\)' Common2026/Shannon/BrunnMinkowski*.lean | wc -l
  rg -nw 'sorry' Common2026/Shannon/BrunnMinkowski*.lean
  ```
- [ ] **V.3** 親 plan banner 更新:
  - `brunn-minkowski-moonshot-plan.md` 末尾「Full genuine closure (後続 plan)」節に本 plan へのポインタ追記
    (closure plan + from-epi plan の 2 本目併設、本 plan を「honesty 強化 sweep」として 3 本目に並べる)。
  - `brunn-minkowski-closure-plan.md` 判断ログに本 plan との関係 (closure plan 領域は touch しない、
    `brunn_minkowski_entropy_jointPi` / `brunn_minkowski_volume_indicator` の tag 整理は本 sweep で
    判断委任) を append。
- [ ] **V.4** **Wall name register R4 拡張提案を別 PR で起草** (`docs/audit/audit-tags.md`「Wall name register」表):
  - `wall:n-dim-prekopa-leindler` — n-dim PL の Fubini 帰納 (`BrunnMinkowskiFunctional.lean:210
    prekopa_leindler_inequality` + closure plan `IsSlicePLReadyHyp` で関連)
  - `wall:bm-convex-body-sqrt` — 凸体 BM sqrt 形 `volAB^(1/n) ≥ volA^(1/n) + volB^(1/n)`
    (`BrunnMinkowski.lean:247 brunn_minkowski_convex_body` + closure plan `IsBMEntropyPowerVolumeHyp` で関連)
  - これらは本 plan の commit には含めず、別 PR で audit-tags.md を拡張 + 本 plan の `@residual(plan:...)`
    タグを `@residual(wall:...)` に migration する後続 patch を予告。
- [ ] **V.5** Pilot 知見を `.claude/handoff-sorry-migration.md` または後続 family plan 用テンプレートに反映:
  - **cross-family direction conflict** (closure plan / from-epi plan との方向衝突) は本 sweep の主要
    operational concern。後続 family (EPI/Stam) でも同様の direction conflict が予想される ため Pilot Pattern Q として記録候補。
  - 「**tier 5 defect の sorry 化が impact 大** (Concavity 11 + Functional 6 transitive)」を実例として記録。
  - 「**boundary tier 5 (`@audit:suspect` の中に隠れた `:= h_xxx` 循環)**」は Hoeffding 起源 Pilot Pattern F の延長、
    BrunnMinkowski で 4 件追加発生を実例として記録。

## 撤退ライン

- **L-MIG-1 (variational / regularity bundle hyp が auditor で load-bearing 判定された場合)**:
  Phase 1 の 5 件 (PLBody) + 2 件 (LayerCake) について auditor が「`IsPL11DSuperLevelHyp` /
  `IsPL1AdditiveHyp` / `IsTailIntegrableHyp` は achievability/converse 本体と等価」と判定したら、
  それらを Phase 2 相当の処理 (body sorry + `@residual(plan:brunn-minkowski-sorry-migration-plan)`、
  signature の regularity hyp は **残す**) に降格。Phase 1 のタグ削除のみは undo。
  - 特に `IsPL2FubiniSliceHyp` (`BrunnMinkowskiPLBody.lean:241`、scalar 等式 placeholder) は本 sweep の
    境界例、auditor が「実 Fubini 未接続の旧 placeholder としての load-bearing」と判定したら
    `@audit:retract-candidate(load-bearing-predicate-placeholder)` + Phase 2 で当該 declaration に
    `@residual(plan:brunn-minkowski-sorry-migration-plan)` 強制付与。

- **L-MIG-2 (Phase 2 で predicate 削除すると依存先で大量に signature drift が起きる場合)**:
  `IsBrunnMinkowskiEntropyHypothesis` の使用箇所が **Concavity 11 + Functional 6 = 17 件** で広範。
  Phase 2.1 で `IsBrunnMinkowskiEntropyHypothesis` を削除すると Concavity / Functional の 17 件すべての
  signature が drift。本 plan のデフォルトは predicate を **削除せず `@audit:retract-candidate` 付与**
  + `brunn_minkowski_entropy_inequality` の body だけ sorry 化 (signature `h_bm_entropy_assumed` 削除)。
  これでも Concavity / Functional 17 件は upstream の type-check 経由で transitive sorry に降格できる。
  - もし此処で **transitive sorry 整合が破綻** (Lean が型推論で sorry 伝播を拒否、または別の compile error
    を出す) なら、Phase 2.1 を中断 + Phase 2 全体を **Phase 2.2 / 2.3 (downstream consumer の signature
    sorry 化)** から先行する逆順に切替 → 未決事項 #1 を user に escalate。

- **L-MIG-3 (closure plan / from-epi plan との方向衝突)** ⚠ **本 plan の最大 operational risk**:
  - **closure plan との衝突**: closure plan は entropy 形 BM `brunn_minkowski_entropy_inequality_genuine`
    (`BrunnMinkowskiClosure.lean:531`) + scaledMul 版 `:695` を **genuine chain で publish 済**
    (4 honest hyp `IsUniformOnEntropyLogVol` 3 + `IsBMEntropyPowerVolumeHyp` 1 のみに縮約)。
    本 sweep が `BrunnMinkowski.lean:192 brunn_minkowski_entropy_inequality` を sorry 化しても、
    closure plan の genuine version (`brunn_minkowski_entropy_inequality_genuine`) は **独立に閉じる**
    (旧 abstract `h` 版 vs concrete `jointDifferentialEntropyPi` 版で signature が異なる)。**衝突しない**
    と判定。
  - **from-epi plan との衝突**: from-epi plan は **未着手**、Phase 0-4 すべて 📋。本 sweep が
    `BrunnMinkowski.lean:192` を sorry 化すると from-epi plan の Phase 4 restate (`brunn_minkowski_entropy_inequality_from_epi`)
    の target signature と一致しなくなる。**衝突あり** — 但し from-epi plan 自体が未着手なので、本 sweep
    完了後に from-epi plan の Phase 4 を「**新 file `BrunnMinkowskiFromEPI.lean` に独立 publish**」する
    形に refine すれば回避可能。本 sweep では from-epi plan を **touch しない** (判断ログに記録)。
  - **scope 縮小判断**: 本 sweep の Phase 2.1 (tier 5 defect 2 件) は当該 declaration の signature
    変更が広範に波及するため、**(a) 本 sweep を `BrunnMinkowski.lean` だけで止める** / **(b) Phase 2.1
    を pause + closure plan Phase V cleanup を先行**、の 2 択を Phase 0 で user 判断仰ぐ可能性あり
    (未決事項 #2)。

- **L-MIG-4 (Approach 変更: pilot scope を縮める)**: Phase 2 が 1 セッションで完走しない /
  honesty-auditor が DEFECT を多発させる場合、`BrunnMinkowski.lean` 5 件のみで pilot を close し、
  Functional / Concavity / PLBody / LayerCake / Closure は後続 sweep として別 plan に分離。
  - 最小 scope (`BrunnMinkowski.lean` 5 件) で達成される honesty 改善: tier 5 defect 2 件解消、
    P-1/P-2 系 3 件解消。残り 35 件は legacy のまま、後続 sweep で対応。

## 未決事項

1. **`IsBrunnMinkowskiEntropyHypothesis` / `IsUniformOnEntropyLogVolHypothesis` / `IsMinkowskiSumMeasurableHypothesis`
   の deprecate 方針**: Phase 2 で全 consumer が `sorry` 化された場合、predicate 定義は
   (a) 削除する / (b) `@audit:retract-candidate` 付きで残す / (c) public API として残し続ける、のどれを選ぶか。
   本 plan のデフォルトは **(b)** (Pilot Hoeffding と同様)。`IsBrunnMinkowskiEntropyHypothesis` の
   17 consumer 整合性が決め手。user の確認待ち。

2. **closure plan との重複領域 (`BrunnMinkowskiClosure.lean:373` / `:493`) の tag 状態**:
   closure plan が **Phase V cleanup 待ち** (`@audit:suspect` 2 件 + 散文 `🟢ʰ` 残置中) であるため、
   本 sweep で `@audit:retract-candidate(closure-plan-completed)` 付与するか、closure plan Phase V cleanup
   と協調するか、auditor 委任。本 plan のデフォルトは **本 sweep で touch せず、closure plan Phase V cleanup
   を先行**。但し本 sweep が closure plan より先に走る場合は本 plan の Phase 2.5 auditor で判断。

3. **`from-epi-discharge plan` との関係 (本 sweep が `BrunnMinkowski.lean` を sorry 化することの影響)**:
   from-epi plan の Phase 4 restate target signature が本 sweep の sorry 化で changed する。本 plan の
   方針は「from-epi plan は本 sweep 完了後に **新 file `BrunnMinkowskiFromEPI.lean` で独立 publish**
   する形に refine する」。user の合意確認。

4. **proof done を本 plan で目指さない方針の明示確認**: 本 plan の DoD は **type-check done** のみ。
   n-dim PL Fubini 帰納 / 凸体 BM の Mathlib 不在は **未着手のまま**で本 plan は close する。
   `brunn-minkowski-moonshot-plan.md` の pass-through publish 状態は変えない (signature 互換、
   旧版 deprecate 化は本 plan scope 外)。user の合意確認。

5. **Wall name register R4 拡張 (`wall:n-dim-prekopa-leindler` + `wall:bm-convex-body-sqrt`)**:
   本 plan の commit に同梱せず、別 PR で `docs/audit/audit-tags.md` を拡張 + 本 sweep の対象
   declaration を `@residual(plan:...)` から `@residual(wall:...)` に migrate する後続 patch を起草するか。
   user の合意確認。

6. **既存 `sorry` 1 件 (`BrunnMinkowskiLayerCakeBody.lean`) の正体**:
   `rg -nw 'sorry'` で hit した 1 件が実 sorry か docstring 文字列か (Pilot Pattern D) を
   inventory step で verbatim 再確認。実 sorry なら Phase 1 で `@residual` 付与、docstring 文字列なら
   無視。

7. **境界 tier 5 4 件 (`BrunnMinkowskiFunctional.lean:432, :458, :503, :586`) の判定境界**:
   body が `:= h_xxx` で循環している (`@audit:suspect` で legacy 計数されているが実は tier 5 defect)。
   Phase 2.3 で `@residual(defect:circular)` を付与するか `@residual(plan:brunn-minkowski-sorry-migration-plan)`
   で済ませるか、implementer の verbatim 確認 + auditor verdict 待ち。

8. **declaration 数 (本 plan 40 件 vs spec 46 件)**: 本 plan の inventory は declaration-level の
   verbatim 抽出で 40 件、spec の 46 件と差分。spec は散文 `🟢ʰ` の docstring 内出現を独立に計数した
   可能性 (例: `BrunnMinkowski.lean:177` の theorem docstring 中の `🟢ʰ` + `:140`, `:169`, `:200`,
   `:232` の structure docstring 中の `🟢ʰ` 等)。本 plan は **declaration を単位** とするため、
   docstring 内の散文 `🟢ʰ` は declaration と pair で対応するものを 1 件として計数。差分の 6 件は
   declaration を共有する複数散文 marker の重複計数と判定。Phase 1.5 auditor で再確認。

## 判断ログ

書く頻度: 方針変更 / 撤退ライン発動 / 当初仮定の修正があったとき。append-only。

1. **2026-05-25 plan 起草**: lean-planner agent が `Common2026/Shannon/BrunnMinkowski*.lean` 6 file の
   legacy marker (suspect 28 + defer 2 + staged 1 + defect 2 + 散文 `🟢ʰ` 多数) を verbatim 読込で
   per-declaration 分類。declaration-level で 40 件と確定 (spec 46 件との差分は散文重複の可能性、
   未決事項 #8 で再確認)。Pattern P-1/P-2/V/C/structure/closure-plan-territory の 5 大カテゴリに分類。
   既存 closure plan (entropy 形 BM genuine 着地済) + from-epi plan (未着手) との方向衝突を identify、
   本 sweep は **closure plan 領域 (`BrunnMinkowskiClosure.lean:373/:493`) を touch しない** + **from-epi
   plan の Phase 4 restate target を新 file 化する形に refine する想定** を判断ログに記録。Wall name
   register R4 拡張提案 2 件 (`wall:n-dim-prekopa-leindler` + `wall:bm-convex-body-sqrt`) を別 PR 化候補と
   して未決事項に escalate。**最大 operational risk** は L-MIG-3 (closure plan / from-epi plan との方向衝突)。

<!-- 後続セッションで判断変更があれば下記に追記 (append-only):
2. **YYYY-MM-DD <要点>**: <変更理由 + 撤退ラインへの紐付け>。
-->
