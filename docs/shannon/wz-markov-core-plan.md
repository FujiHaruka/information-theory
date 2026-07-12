# Wyner–Ziv: Markov-core (conditional-AEP) 実装サブ計画

> **Parent**: [`wz-binning-covering-plan.md`](wz-binning-covering-plan.md) §Leg F

> **STATUS 2026-07-12 (Leg 13) — Markov-core 全体 CLOSED (machine-verified sorryAx-free)、残 = Atom G のみ**:
> Atom E+F coupled (`d8954711`) で Ecov を strong-at-ε_cov ∩ weak-at-ε に強化 (radius separation
> `ε_cov=ε/(2(1+C))`、判断ログ #4、監査 SOUND、`@audit:defect` 4 件除去) → core wrapper sorry-free
> (`b489d51f`) → **conditional-AEP kernel `wz_covering_uyBand_condSlice_le` genuine 閉** (`e4490dbb`)。
> **Markov-core chain (kernel/wrapper/outer/inner/leaf + helper `wz_sum_eq_typeCount_mul`) が独立 `#print axioms`
> で `[propext,Classical.choice,Quot.sound]` = sorryAx-free 確認済**。**headline `wyner_ziv_achievability` に残る
> 唯一の sorry = Atom G covering atom `wz_coveringFamily_of_testChannel` (~L1154)**。両閉じで headline sorryAx-free。
> #9 crux 維持 (仮説追加なし)。converse (P2) 無影響。詳細 → 下 §Approach + §判断ログ #3/#4 + §Atom G/H。

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
- [x] **Atom E — 核 rewrite** `wz_covering_jointBand_markov_core` (`d8954711`/`b489d51f`/`4449e61f`): statement reframe (Ecov strong 化 + radius separation `ε_cov=ε/(2(1+C))`) 監査 SOUND・`@audit:defect` 除去、**wrapper sorry-free** (Atom A split + good/bad dichotomy + `∑∏P_X=1` 吸収 + weighted sum)。analytic 中核は kernel に isolate ↓ ✅
- [x] **Atom E-kernel — conditional-AEP kernel** `wz_covering_uyBand_condSlice_le` (`e4490dbb`): from-scratch correlated conditional AEP を genuine に閉じた (B1 sup-bound→B2 mean=M→B3 entropy→mean-pin→Atom B δ=ε/2)。新 helper `wz_sum_eq_typeCount_mul` (method-of-types reindexing) 抽出。**Markov-core chain 全体 (kernel/wrapper/outer/inner/leaf + helper) が machine-verified sorryAx-free** (`#print axioms` = `[propext,Classical.choice,Quot.sound]`、独立確認)。wrapper stale `@residual` 除去。**残 sorry = Atom G の covering atom のみ** ✅
- [x] **Atom F — chain 伝播** outer/inner/leaf の `Ecov` を同時 strong 化 + reduction 再証明 (`d8954711`)、sorry-free reduction・`@audit:defect` 3 件除去・独立監査 PASS ✅
- [ ] **Atom G — covering atom 配線** `wz_coveringFamily_of_testChannel` が **strong-at-ε_cov ∩ weak-at-ε** covering-success を w.h.p. 供給するよう reopening (plain strong-at-ε でない、下 §Atom G 参照)、strong-Ecov leaf consume で atom の sorry 閉 📋
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

- [x] core の covering-success 事象 `Ecov` を weak `jointlyTypicalSet` → **strong-at-ε_cov ∩ weak-at-ε**
  (`wzCoveringSuccessStrong`) に変更 (`d8954711`、監査 SOUND)。**残 = body の sorry-free 化** (下 recipe)。
- **radius separation (`d8954711`、必須)**: strong を acceptance band と同じ ε で取ると mean-pin は
  `|M(xb)−H(wsm)| ≤ C·ε` (`C = ∑_p |wzCondMeanKernel|` = gateway 増幅定数、一般に `C≫1`) しか出ず、
  O(ε) 部分 relabel class が `Euy` に生存 (class-not-instance)。∴ strong conjunct を **`ε_cov = ε/(2(1+C))`**
  (`wzCoveringStrongRadius` ~L5721) で取り `C·ε_cov < ε/2` を保証、weak conjunct は ε のまま plumbing 用。
  `ε_cov` は computed def ゆえ署名不変。→ facts の radius-separation 行 + 判断ログ #4。
- **証明 recipe (body)**: Atom A (`wz_srcBlock_condMeasure_split`) で `SRC.real(triple-∩)` を
  `∑ xb (∏ᵢ P_X(xb_i)) · condY(xb).real(slice)` に還元 → good xb (strong-cover at ε_cov ∧ (x,y)-typ) で
  mean-pin gateway `wz_wsm_negLog_mean_pin_of_stronglyTypical` により `|M(xb)−H(wsm)| < ε/2` を得、Atom B engine
  (`wz_pi_nonuniform_mean_concentration` / `_concentration_tendsto`) の Chebyshev を **δ=ε/2** で適用し empirical
  (u,y)-entropy を `M(xb)` 周りに集中 → 三角で `|emp(u,y)−H(wsm)| < ε` ⟹ `Euy` に入らない → bad xb は
  condY `≤1` + `∑ xb ∏ P_X = 1` で吸収 → `≤ tol/8`。
- **旧 weak-Ecov で false だった Atom B(per-xb)+Atom D が strong-Ecov + mean-pin で sound 化** — gateway が
  `M(xb)` 転送を供給するため、集中先が `H(wsm)` に固定される。
- `Nonempty (α'×Fin k)` は qStar/full-support から導出 (署名変更不要、gateway 実装者確認済)。
- **honesty**: 完了時に core の `@audit:defect(false-statement)` を除去。3 hyps (`hκ'_pos`/`hκ'_sum`/`hqStar`)
  は precondition threading で維持 (bundling でない)。
- **tractability**: med-large (本 build の genuine 本番)。撤退 = `sorry + @residual(plan:wz-binning-covering)`。
- **DONE (`b489d51f`)**: wrapper (Atom A split + good/bad dichotomy + `∑∏P_X=1` 吸収 + weighted sum) は sorry-free。
  bad xb = strong-cover conjunct 失敗 ⟹ slice empty ⟹ mass 0。good xb = kernel consume。analytic 中核 (step 2-4)
  は kernel `wz_covering_uyBand_condSlice_le` に isolate ↓。

### Atom E-kernel — conditional-AEP kernel (`wz_covering_uyBand_condSlice_le`、~L5797、最難所、active mainline)

**proof-log: yes** (from-scratch correlated conditional AEP の build 根拠)

- [x] **DONE (`e4490dbb`)**: kernel を genuine に閉じた (下 recipe 通り、design backtrack なし、Mathlib gap なし)。
  helper `wz_sum_eq_typeCount_mul` 抽出。独立 `#print axioms` で sorryAx-free 確認。以下は build recipe (再開不要、記録)。
- statement = good xb (strong-cover at ε_cov ∧ (x,y)-typ) 下で
  `condY(xb).real({(u,y)-block が Euy = ε-atypical}) ≤ tol/8`。u = `c.decoder(c.encoder xb)` は x-block 全体の
  関数ゆえ `(uᵢ,yᵢ)` は iid でも独立でもない = **correlated conditional method-of-types concentration** (plain
  `aep_chebyshev_bound` 不適)。
- **recipe (実装報告、in-tree template `wz_covering_yBand_aep`)**:
  - `ψ i y := pmfLog (rdAmbient wsm) (jointSequence iidXs Ycoerce) (Uᵢ, y)` (`= −log(law{(Uᵢ,y)})`)、
    `νᵢ := pmfToMeasure(P(·|xbᵢ))`。
  - **B1 sup-bound**: `|ψ i y| ≤ B := ∑_q |log(wsm q)|` (via `wzSideInfoMarginal_pos` + coerced-law singleton
    `law{(u,coerce y')} = wsm(u,y')` / off-image 0)。
  - **B2 mean=M**: `∫ψᵢ dνᵢ = wzCondMeanKernel(xbᵢ,Uᵢ)` (pmfToMeasure 積分 = 有限和、off-subtype y は
    `P_XY{(x,y)}=0` で 0 寄与) ⟹ `(∑ᵢ∫ψᵢ)/n = ∑_p (typeCount zb p/n)·wzCondMeanKernel = M(xb)` (gateway 形、
    `zb=(fun i↦(xbᵢ,Uᵢ))`)。
  - **B3 entropy**: `entropy(rdAmbient wsm)(jointSeq 0) = ∑_q negMulLog(wsm q) = H(wsm)` (via
    `wz_entropy_map_injective` の `id×coerce` relabel + `rdAmbient_map_jointSequence`)。
  - **mean-pin**: `wz_wsm_negLog_mean_pin_of_stronglyTypical` on `hgood` (半径 ε_cov) ⟹ `|M(xb)−H| ≤ C·ε_cov < ε/2`。
  - **inclusion + Atom B**: `Euy = {ε ≤ |(∑ψᵢ(yᵢ))/n − H|} ⊆ {ε/2 ≤ |(∑ψᵢ)/n − M(xb)|}` (三角)、
    `wz_pi_nonuniform_concentration_tendsto (B) (δ=ε/2) (tol/8)` で condY の RHS 質量を `tol/8` で bound。
    `N` は `∀ xb` の前で一様に選ぶ。
- **fiddly**: coerced-joint-law pushforward + B2 subtype 拡張。Mathlib gap なし (全 bridge に in-tree template)。
- **honesty**: 撤退口 = `sorry + @residual(plan:wz-binning-covering)`。bundling 禁止 (concentration を仮説で受けない)。
- **tractability**: med-large (最難所)。~150-250 行。

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

- [ ] covering atom `wz_coveringFamily_of_testChannel` の construction を、**`wzCoveringSuccessStrong` =
  strong-at-ε_cov ∩ weak-at-ε covering-success を w.h.p. で供給**するよう配線 (plain strong-at-ε でない、
  radius separation `ε_cov=ε/(2(1+C))` 由来 — `d8954711`) → strong-Ecov leaf を consume して atom の sorry を閉じる。
  下界は strong-at-ε_cov 側で効く (weak-at-ε は strong ⊆ weak で自動)。
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
- [ ] **Markov-core chain の `@audit:ok` stamp**: kernel/wrapper/outer/inner/leaf は sorryAx-free 確定 (Leg 13、
  wrapper stale `@residual` は `e4490dbb` 後の Leg 13 で除去済) → closure 監査後に `@audit:ok` を付与。
  historical prose (wrapper docstring ~66 行の weak-covering false-as-framed episode) の compaction も検討。
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
4. **strong-at-same-ε も依然 false → radius separation `ε_cov=ε/(2(1+C))` が必須、独立監査 PASS (2026-07-12、
   active、決定的)**: Ecov を strong typicality に強化する際、acceptance band と**同じ半径 ε** で取ると mean-pin
   gateway は `|M(xb)−H(wsm)| ≤ C·ε` (`C=∑_p|wzCondMeanKernel|` = 全 (x,u) 対上の条件付き交差エントロピー和、
   一般に `C≫1`) しか出ず、O(ε) の**部分** relabel (縮小 label-swap) が (u,y) empirical entropy を `C·ε≫ε`
   ずらして `Euy` に着地 = **class-not-instance トラップ** (前回の #3 教訓「1 反例では class が残る」の再演)。
   実装が naive same-ε 版 (`55ce7dbb`) を commit 後に自力発見し、**radius separation** で修正 (`d8954711`):
   strong conjunct を `ε_cov=ε/(2(1+C))` (`wzCoveringStrongRadius`) で取り `C·ε_cov=(C/(1+C))·(ε/2)<ε/2`
   (strict ∀C≥0)、weak conjunct は ε のまま (`wz_covering_success_subset_uTypical` plumbing 用)。`ε_cov` は
   ε/κ'/P_XY の computed def ゆえ chain 署名不変。独立 honesty-auditor が **class-level closure** (ε_cov-ball
   全体で mean-pin 一様 `<ε/2`、別 class 非生存、mean-pin+Atom-B concentration の三角が strict に閉じる) を確認し、
   `@audit:defect(false-statement)` 4 件除去を **justified** と verdict (core docstring L5854 に PASS note)。
   `wzCoveringSuccessStrong=strong-at-ε_cov ∩ weak-at-ε` は正当な WZ tradeoff (Markov-core 易化 / covering 難化)。
   **Atom G への含意**: covering atom は今や strong-at-ε_cov ∩ weak-at-ε を供給する必要 (§Atom G 更新済)。
   **教訓**: gateway の conclusion 形 `|…| ≤ (∑|wzCondMeanKernel|)·ε` を verbatim 読めば「strong pins M to H」
   の prose だけでは隠れる増幅定数 C が見え、same-ε 不十分は build 前に検出できた (Mathlib-shape-driven の
   conclusion-verbatim 原則が effective)。settled は `wz-facts.md` radius-separation 行。
