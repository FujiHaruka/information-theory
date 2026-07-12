# Wyner–Ziv: Markov-core (conditional-AEP) 実装サブ計画

> **Parent**: [`wz-binning-covering-plan.md`](wz-binning-covering-plan.md) §Leg F

> **STATUS 2026-07-12 (Leg 12+) — Proposal A GO 確定、strong-Ecov build 進行中**:
> gateway `wz_wsm_negLog_mean_pin_of_stronglyTypical` (~L5403) が sorry-free + sorryAx-free で landing
> (`7812cfcf`)。**strong typicality が empirical type を TV で pin ⟹ 条件付き平均 `M(xb)` が `H(wsm)` に pin
> される**を機械確認 — 弱 typicality で label-swap 反例により偽だった crux が strong で成立。これで
> 「弱 Approach INVALIDATED、user-decision フォーク」は解消し、**Proposal A (strong `Ecov`) の実行が確定路**。
> 残 = strong-Ecov build (Atom E-H)。headline `wyner_ziv_achievability` に仮説追加なし (#9 crux 維持)。
> converse (P2) は無影響 (FULLY CLOSED sorryAx-free)。詳細 → 下 §Approach + §判断ログ #3 + `wz-facts.md`。

## Context

WZ achievability chain 唯一の genuine hard residual = C2 covering-acceptance の核。中枢は
`wz_covering_jointBand_markov_core` (`InformationTheory/Shannon/WynerZiv/Achievability.lean`、位置は
`scripts/sig_view.ts --sorry` で都度)。選ばれた covering word `U = c.decoder (c.encoder x-block)`
(= x-block 全体の deterministic 関数) と相関 side-info `Y` が jointly `(U,Y)`-atypical になる事象の
SRC-measure 上界。**class `plan`、NOT a Mathlib wall**。難所は `(U_i, Y_i)` が iid でも独立でもないため
plain `aep_chebyshev_bound` (IdentDistrib 前提) が効かない点 = conditional AEP (Markov lemma U—X—Y)。

**現状の 2 事実**: (1) core→outer→inner→leaf の 4 decl は **weak (entropy-only) typicality の `Ecov`
の下で FALSE-AS-FRAMED** (`@audit:defect(false-statement)` 4 件、`1ddc2887`、label-swap 反例)。
(2) **gateway `7812cfcf` が strong typicality で crux を機械確認** — strong `Ecov` に強化すれば false
cluster が sound 化する。∴ 残作業 = `Ecov` を weak `jointlyTypicalSet` → `jointStronglyTypicalSet` に
差し替えて chain 全体を sorry-free 化する (Proposal A、下 §Approach)。

## 進捗

- [x] M0 API 確認 — finite-Fubini + `IndepFun.variance_sum` + Chebyshev tail 確定 ✅
- [x] Atom C — mean-identity 群 sorry-free (`ef34494a`) + gateway 版 mean-identity `wz_wsm_condMean_kernel_inner_eq_entropy` (~L5302) ✅
- [x] Atom A — finite Fubini split `wz_srcBlock_condMeasure_split` (~L5504)、sorry-free (`95a07fa4`)。**再利用可能・不変** ✅
- [x] Atom B engine — 非-iid conditional-Chebyshev primitive 2 本 `wz_pi_nonuniform_mean_concentration` (~L5572) / `wz_pi_nonuniform_concentration_tendsto` (~L5656)、sorry-free (`1b5be107`/`469ae6f2`)。**再利用可能・不変** ✅
- [x] **gateway (Proposal A crux) — `wz_wsm_negLog_mean_pin_of_stronglyTypical` (~L5403) + 支援 3 本 (`wzCondMeanKernel` ~L5289 / `wz_wsm_condMean_kernel_inner_eq_entropy` ~L5302 / `wz_wsm_negLog_mean_pin_of_type` ~L5365) sorry-free + sorryAx-free** (`7812cfcf`)。strong typicality → `M(xb)` を `H(wsm)` に pin ✅
- [ ] **Atom E — 核 rewrite** `wz_covering_jointBand_markov_core` の `Ecov` を strong 化 + sorry-free、`@audit:defect(false-statement)` 除去 (E+F coupled、本線) 🚧
- [ ] **Atom F — chain 伝播** outer/inner/leaf の `Ecov` を同時 strong 化 + reduction 再証明 (E と COUPLED) 🚧
- [ ] **Atom G — covering atom 配線** `wz_coveringFamily_of_testChannel` が strong covering-success を w.h.p. 供給するよう reopening、strong-Ecov leaf consume で atom の sorry 閉 📋
- [ ] **Atom H — PV + closure** `#print axioms wyner_ziv_achievability` sorryAx-free 確認 + README + plan closure 同期 📋

## ゴール / Approach

### Goal

C2 covering-acceptance chain (core→outer→inner→leaf→covering atom) を strong `Ecov` に載せ替えて
全 sorry を genuine 除去し、`wyner_ziv_achievability` を sorryAx-free
(`[propext, Classical.choice, Quot.sound]`) へ到達させる。headline 署名は不変 (#9 crux、strong typicality
の強度は**定義由来**であって headline への仮説追加ではない)。撤退口は `sorry + @residual(plan:wz-binning-covering)`
のみ (bundling 禁止)。

### Approach — strong-Ecov build (solution shape)

弱 Approach (Atom C/A/B/D on weak `typicalSet`) の**唯一の破綻点は `Ecov` の typicality 強度**だった:
弱 `typicalSet` = `{|CE(type,law)−H(law)|<ε}` は type の scalar entropy 汎関数のみ pin し TV では pin
しないため、Atom C の恒等式 `⟨qStar-weight, g⟩ = H(wsm)` を条件付き平均 `M(xb)=⟨type_xu, g⟩` に転送でき
なかった (entropy 保存 label-swap relabel が qStar と同じ 3 entropy を持ちつつ `M(xb)` を乖離させる)。

**gateway (`7812cfcf`) がこの転送を strong typicality で復活**させた: `jointStronglyTypicalSet` は
per-symbol TV で `type_xu ≈ qStar` を pin ⟹ 任意の有界線形汎関数 (特に `M(xb)`、g は `wsm>0` ゆえ有界)
が `⟨qStar, g⟩ = H(wsm)` に pin ⟹ label-swap 反例が死ぬ (非-qStar conditional は strong-typical でない)。
∴ **修正 = `Ecov` のみ weak → strong に強化**、`Euy`/`Exytyp` は弱のまま。build の骨格:

- **Atom A (finite Fubini split) + Atom B engine (conditional Chebyshev) はそのまま再利用** — SRC の
  x-block disintegration も非-iid 分散集中も `Ecov` の強度に依存しない機構。
- **good xb** (strong-cover ∧ (x,y)-typ) で **mean-pin gateway** (`M(xb)≈H(wsm)`) + **Atom B engine**
  (condY 上の Chebyshev で empirical (u,y)-entropy を `M(xb)` 周りに集中) ⟹ `Euy` small。
- **bad xb** は `∑ xb ∏ P_X = 1` で吸収 → 全体 `≤ tol/8`。
- chain 上流 (outer/inner/leaf/covering atom) は `Ecov` の強度定義を差し替えて union-bound 構造を再証明
  (strong ⊆ weak ゆえ measure 単調で概ね通る) + covering 構成が strong-typical codeword を w.h.p. 供給する
  よう reopening。

**coupling 制約 (最重要、mechanically 確認済)**: `Ecov` の typicality を core で weak→strong に変えると、
consume 関係 core→outer→inner→leaf→covering atom が一緒に変わらないとコンパイルが壊れる (file-internal
`private` chain、grep で確認: outer が core を、inner が outer を、leaf が inner を、covering atom が leaf を
consume)。**∴ Atom E (核 rewrite) と Atom F (chain 伝播) は 1 つの coupled 変更として扱う** — 同一 dispatch
or 連続 dispatch で、file を常に type-check-done に保つ。ripple は Achievability.lean file-contained
(cross-file consumer 0、headline 署名不変)。

## Phase 詳細

各 atom は Achievability.lean 内 `private lemma` の rewrite/追加。`open ChannelCoding in` scope 内。
conclusion 形は Mathlib 出口形に合わせる (「Mathlib-shape-driven」)。位置は `sig_view --sorry` で都度確認。

### Atom E — 核 rewrite (`wz_covering_jointBand_markov_core`、本線、E+F coupled)

**proof-log: yes** (from-scratch concentration の再証明、再開根拠に必須)

- [ ] core の covering-success 事象 `Ecov` を weak `jointlyTypicalSet` → `jointStronglyTypicalSet` に変更し
  body を sorry-free 化。
- **証明 recipe**: Atom A (`wz_srcBlock_condMeasure_split`) で `SRC.real(triple-∩)` を
  `∑ xb (∏ᵢ P_X(xb_i)) · condY(xb).real(slice)` に還元 → good xb (strong-cover ∧ (x,y)-typ) で
  mean-pin gateway `wz_wsm_negLog_mean_pin_of_stronglyTypical` により `M(xb)≈H(wsm)` を得、Atom B engine
  (`wz_pi_nonuniform_mean_concentration` / `_concentration_tendsto`) の Chebyshev で empirical (u,y)-entropy
  を `M(xb)` 周りに集中 ⟹ `Euy` small → bad xb は condY `≤1` + `∑ xb ∏ P_X = 1` で吸収 → `≤ tol/8`。
- **旧 weak-Ecov で false だった Atom B(per-xb)+Atom D が strong-Ecov + mean-pin で sound 化** — gateway が
  `M(xb)` 転送を供給するため、集中先が `H(wsm)` に固定される。
- `Nonempty (α'×Fin k)` は qStar/full-support から導出 (署名変更不要、gateway 実装者確認済)。
- **honesty**: 完了時に core の `@audit:defect(false-statement)` を除去。3 hyps (`hκ'_pos`/`hκ'_sum`/`hqStar`)
  は precondition threading で維持 (bundling でない)。
- **tractability**: med-large (本 build の genuine 本番)。撤退 = `sorry + @residual(plan:wz-binning-covering)`。

### Atom F — chain 伝播 (outer / inner / leaf、Atom E と COUPLED)

**proof-log: yes** (伝播の sound 性が再開根拠)

- [ ] outer `wz_covering_jointBand_concentration` / inner `wz_covering_markov_concentration` / leaf
  `wz_covering_chosenWord_sideInfo_typical` の `Ecov` を**同時に** strong 化し reduction を再証明。
- union-bound 構造は不変 (`measureReal_union_le`、strong ⊆ weak ゆえ measure 単調で概ね通る見込み)。
  leaf は既に genuine outer decomposition (`AcceptFail ⊆ CoveringFail ∪ (cover-success ∩ AcceptFail)`) 形
  ゆえ、内側の cover-success を strong に差し替えるのみ。
- **honesty**: 各 decl の `@audit:defect(false-statement)` を除去 (計 outer/inner/leaf の 3 件、core と併せ 4 件)。
- **coupling 制約 (再掲)**: E を変えると outer→inner→leaf の型が壊れるため、E と同一 dispatch or 連続で扱い、
  file を type-check-done に保つ。各 sorry-ify 撤退口 = `sorry + @residual(plan:wz-binning-covering)`。
- **tractability**: med (機械寄り、strong→weak subset の measure 単調が主機構)。

### Atom G — covering atom 配線 (reopening、G の下界が主リスク)

**proof-log: yes** (covering-success 下界の reopening が再開根拠)

- [ ] covering atom `wz_coveringFamily_of_testChannel` の construction を、**strong covering-success を
  w.h.p. で供給**するよう配線 → strong-Ecov leaf を consume して atom の sorry を閉じる。
- **素材**: `jointStronglyTypicalSet_indep_prob_ge` (`RateDistortion/AchievabilityJointStrongTypicality.lean:474`、
  strong-typical 独立積の質量下界、type-class 前提 = full support `hposX/Y/Z` + iid/ident/pairwise-indep) +
  `wz_jointStronglyTypical_mem_distortionTypical` (~L603、既に joint strong typicality を distortion 側で
  consume する手本) + `jointStronglyTypicalSet_implies_X/Y_stronglyTypical` (166/250) +
  `stronglyTypicalSet_subset_typicalSet` (`StrongTypicality.lean:429`、strong→weak bridge)。RD sibling
  `AchievabilityStrongTypicality/` に類似 machinery の前例。
- **gateway-atom-first の再適用ポイント**: strong covering-success 下界を **1 補題で先に試す**
  (`jointStronglyTypicalSet_indep_prob_ge` の WZ-instance)。通れば reopening 全体が plumbing で閉じる、
  通らなければ当該補題のみ shared sorry に縮退 (撤退)。
- ⚠ **reorder 注意**: leaf は file 末尾、covering atom は前方 (L1154) → leaf を前に出すか D2-transport hoist
  (旧 handoff Task #5 参照)。
- **stale docstring 訂正**: covering atom の code docstring が旧「S5a/gateway-2 Fubini derandomize」機構を記述
  = STALE、consume 配線時に訂正 (code がタグ SoT)。
- **tractability**: med-large (reopening が主リスク)。撤退 = `sorry + @residual(plan:wz-binning-covering)`。

### Atom H — PV + closure

**proof-log: no**

- [ ] 全 sorry 消滅で `#print axioms wyner_ziv_achievability` = `[propext, Classical.choice, Quot.sound]` を機械確認。
- [ ] `honesty-auditor` 独立監査 (defect 除去 + strong-Ecov chain の honesty 4-check、orchestrator-mandatory)。
- [ ] `gen_readme_table.ts` README Ch.15 表登録 + 子 `wz-binning-covering-plan` / 親 `wyner-ziv-main-plan` /
  moonshot `wyner-ziv-moonshot-plan` の closure 同期。
- **tractability**: easy。

**依存順**: gateway (DONE) → **E+F coupled** (本線) → G (reopening) → H。E+F は 1 変更、G は E+F 完了後、H は最後。
署名変更は headline に及ばず file-contained (ripple 確認済: core→outer→inner→leaf→covering atom、cross-file 0)。

## 再利用可能・不変な資産 (strong-Ecov build で as-is)

- **Atom A** `wz_srcBlock_condMeasure_split` (~L5504、finite-Fubini split、disintegration 回避)。
- **Atom B engine** `wz_pi_nonuniform_mean_concentration` (~L5572) / `wz_pi_nonuniform_concentration_tendsto`
  (~L5656、非-iid conditional Chebyshev)。
- **gateway** `wz_wsm_negLog_mean_pin_of_stronglyTypical` (~L5403) + 支援 3 本 (`wzCondMeanKernel` ~L5289 /
  `wz_wsm_condMean_kernel_inner_eq_entropy` ~L5302 / `wz_wsm_negLog_mean_pin_of_type` ~L5365)。conclusion:
  `|∑_p (typeCount zb p/n)·wzCondMeanKernel − ∑_q negMulLog(wsm q)| ≤ (∑_p |wzCondMeanKernel p|)·ε`、
  subtype α'×Fin k + `κ' p.1.1 p.2 * ∑ y …` の順が core 署名に verbatim 一致。
- **Atom C mean-identity 群** (division-free workhorse + division 形)。

## Cross-family 再利用の判断 (実装者の気づきへの回答)

Markov-lemma パターン (決定的 word `u=f(x-block)`、相関 side-info `y`、atypical joint 集合の UPPER
concentration) は relay-CF / broadcast で再出しうる。**推奨 = WZ-internal で先に build (default、低結合)**:
1 つも working instance が無い段階で shared sorry-lemma primitive に abstract すると結合度が上がる。
audit-tags.md「Proposed wall」register の promote-trigger (2+ family 参照 or closure-plan 整合) に従い、
**WZ instance を proved 化した後**に shared 化 (候補 name 例 `markov-lemma-conditional-aep`) を再判定する。

## 判断ログ

1. **finite-vs-general disintegration = finite Fubini で解決 (active、durable)**: piece (a) は general
   `condDistrib` on `Measure.pi` (0-hit) を要さず、`pmfToMeasure` atomicity + `Measure.pi_pi` +
   `Fintype.sum_prod_type` の有限 Fubini で x-block を factor できる。実装者の condDistrib 0-hit は general
   machinery 側で正しいが off-path。真の bulk は conditional Chebyshev (`IndepFun.variance_sum`、IdentDistrib
   不要)。→ settled は `wz-facts.md`。
2. **危惧された disintegration 壁は CLOSED sorry-free (Atom A `95a07fa4`)**: finite-Fubini 解決を実装で確認、
   `wz_srcBlock_condMeasure_split` が genuine。低優先 TODO: `wz_pi_pmf_real_eq_sum` は `private`
   `measure_pi_eq_sum_singletons` (ShannonTheoremGeneral.lean:410) を再導出、shared lemma 昇格候補。
3. **core は weak typicality で FALSE-AS-FRAMED → strong-Ecov (Proposal A) で解決、gateway で機械確認済
   (2026-07-12、active、決定的)**: 弱 `typicalSet` は type の scalar entropy 汎関数のみ pin し TV では pin
   しないため、covering-success (弱 `jointlyTypicalSet` under qStar) を entropy 保存の label-swap relabel ν が
   満たしつつ `M(xb)=⟨type_xu,g⟩` を `H(wsm)` から乖離させる (∏P_X-mass→1、advisor+独立 auditor が反例を自力
   再計算し confirm、`1ddc2887` で core/outer/inner/leaf に `@audit:defect(false-statement)`、前回 sufficiency
   PASS を overturn)。**修正 = `Ecov` のみ strong joint typicality に強化**: gateway
   `wz_wsm_negLog_mean_pin_of_stronglyTypical` (`7812cfcf`、sorry-free + sorryAx-free) が「strong typicality
   → empirical type を TV で pin → `M(xb)` が `H(wsm)` に pin」を**機械確認** ⟹ label-swap が死ぬ ⟹
   Atom C の恒等式が転送可能 ⟹ 弱で false だった Atom B(per-xb)+Atom D が sound 化。∴ **Proposal A GO 確定**、
   残 = strong-Ecov build (Atom E-H)。Atom A/B engine はそのまま再利用。settled は `wz-facts.md`。
   **教訓**: not-a-wall/hypothesis-OK checklist の「退化境界を 2 つ試す」で constant-word (point-mass κ') に
   加え entropy 保存 relabel を試せば前回監査で捕まえられた — 1 反例のみの監査は under-hyp を pass しうる。
   named textbook object (Markov lemma) は標準仮説の強度 (strong vs weak typicality) を in-project 定義と
   diff すれば build 前に検出できた。
