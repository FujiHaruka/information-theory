# Wyner–Ziv achievability: D3 binning + covering closure サブ計画

> **Parent**: [`wyner-ziv-main-plan.md`](wyner-ziv-main-plan.md) §P3 D3 split-out

**Status**: Proposal A GO 進行中 🚧 (Leg 12+、strong-Ecov build) — **C2 covering chain は weak typicality で FALSE-AS-FRAMED だったが (core→outer→inner→leaf に `@audit:defect(false-statement)` `1ddc2887`、label-swap 反例)、gateway `wz_wsm_negLog_mean_pin_of_stronglyTypical` (`7812cfcf`、sorry-free + sorryAx-free) が strong typicality で crux (`M(xb)` を `H(wsm)` に pin) を機械確認 → Proposal A (strong `Ecov`) GO 確定**。残 = strong-Ecov build (孫 plan Atom E-H、E+F coupled が本線)。詳細 → §Leg F / 孫 plan [`wz-markov-core-plan.md`](wz-markov-core-plan.md) §Approach / `wz-facts.md`。A3/E2b 側は無影響 (下記)。以下は build 前の chain 記述:**A3/E2b 側 CLOSED**: A3 `wz_exists_binning_E2_bound` body genuine sorry-free (r7 `d1f2445a`) + Leg E-mass `wz_source_codeword_sideInfo_mass_le` sorry-free `@audit:ok` (`66417846`/`259ecccc`) ゆえ **A3 sub-tree sorryAx-free**。**C2 covering-acceptance leaf `wz_covering_chosenWord_sideInfo_typical` = r9 で genuine outer decomposition (`AcceptFail ⊆ CoveringFail ∪ (cover-success ∩ AcceptFail)`、`measureReal_union_le`) に再構成 = sorry-free (`9ecffb41`) + false-as-framed fix 後 再監査 ALL-OK (`867972b2`)**: 旧 free-param 形 (qStar/κ' unconstrained) は constant-word 反例で偽 (独立 auditor CONFIRMED `3965ba5e`、旧 `d2e68b10` PASS = free-param 形を tier-2 と誤認していたのを overturn) → full-support/proper-pmf/qStar-κ' consistency の 3 regularity を leaf+inner に threading (precondition-exposure、bundling でない) で TRUE-as-framed 化 (covering atom が 3 者を存在 conjunct として verbatim export ゆえ discharge、headline-safe)。残 literal sorry **2** (両 `@residual(plan:wz-binning-covering)`): (i) inner `wz_covering_markov_concentration` (Markov-concentration kernel、r9 新規 isolate)、(ii) covering atom `wz_coveringFamily_of_testChannel` (leaf を consume 未配線ゆえ自身の sorry 残置)。**inner の build = L0-L5 scaffold (Leg F、L4 Band-Joint conditional concentration が唯一の難所、~150-300行 `plan`-class、wall でない、advisor verdict = few-sessions closable)**。**mainline = inner を L0-L5 で build → leaf を covering atom に consume 配線 (covering-success 分解 + joint derandomize `exists_codebook_low_avg`) + 当該 atom の stale docstring 訂正**。両 sorry closing で `#print axioms wyner_ziv_achievability` sorryAx-free。**A2 `wz_ideal_expectation_eq_covering` `@audit:ok`。Leg 0-E DONE**。位置 (leaf/inner/atom の line) は `scripts/sig_view.ts --sorry` で都度。

**再検証** (prose にキャッシュしない): `scripts/sig_view.ts --sorry InformationTheory/Shannon/WynerZiv/Achievability.lean` / `#print axioms wyner_ziv_achievability`。

## 進捗

- [x] Leg 0 — δ-split 署名修正 (budget 軸、第1 tier-5 fix) ✅ (`a59e37cb`、独立監査 PASS)
- [x] Leg A — two-ambient WZ-joint 構成 (regularity) ✅ (`dfdf3e42`、sorry-free)
- [x] Leg B — α'→α source-measure 変数変換 ✅ (`02ea97d7`、sorry-free)
- [x] Leg C — WZ distortion-decomposition bridge ✅ (`25629b0a`、sorry-free)
- [x] Leg C.5 — D3 署名 reconciliation (`hd'_eq`+`hqf`、第2 tier-5 fix) ✅ (`22b64afa`、独立監査 PASS)
- [x] Leg C.6 — hcov₁ M-pin (M-axis under-hyp fix、第3軸解消) ✅ (`fe3d9482`/`90996ed1`、独立監査 all-PASS、D3 `@audit:defect` 除去 honest tier-2 復帰)
- [x] Leg D — E2-only decomp glue: **G2/A1/A2 DONE** sorry-free (`a5e23439`/`1bb1d1ad`/`84393413`、A2 `@audit:ok`) ✅
- [x] Leg E 署名 rework — pinned-ε 共有 radius threading + dα'-d link、第4/第5軸を署名レベルで closure ✅ (`cf7d57cd`/`42abbf21`、独立監査 all-PASS)
- [x] Leg E-A3 fill — A3 `wz_exists_binning_E2_bound` **body genuine (sorry-free) + 独立監査 PASS** (`d1f2445a`、r7): {decoder≠true}⊆C2∪E2b (`wzBinTypicalDecoder_eq_of_unique` 対偶) + C2 は `hcov_accept` premise + E2b は binning derandomize(`exists_le_integral`)+S5b+exponent decay + `distortionMax dα'≤d` で δ/4。**副産物**: (a) S5b `wz_codebook_confusion_expectation_le` を abstract-`jts` に generalize (measure mismatch: source `Measure.pi` full-β vs decoder ambient β'-subtype、pure relaxation、`@audit:ok` 再確認)、(b) per-codeword mass を新 named atom に isolate ↓
- [x] Leg E-mass — `wz_source_codeword_sideInfo_mass_le` **DONE sorry-free + sorryAx-free + `@audit:ok`** (`66417846` closure / `259ecccc` 監査 PASS、独立監査 PASS): D2 `wz_covering_codeword_sideInfo_mass_le`(`@audit:ok`) を source→ambient に side-info-marginal agreement (n-fold Y-law) + 11 private helper (injective-relabel の mass/entropy 不変・marginal-agreement chain・iid n-fold law・entropy→exponent bridge) で transport。**訂正**: exponent bridge は `wzMutualInfoYU_eq_mutualInfo` (Operational.lean:230) を使わなかった (同 lemma は `q'` を ambient RV の empirical pmf に要求するが、ここでは `q'` は固定 factored pmf) — direct pmf-level `mutualInfoPmf` 計算 (helper `wz_mutualInfoPmf_wzMarginalYU_eq`) を self-build (監査で逸脱 sound 確認)。A3 が S5b の `hmass` に消費 ✅
- [ ] Leg F — C2 covering-acceptance の残核 = inner `wz_covering_markov_concentration` (mainline、L0-L5 scaffold)。**leaf `wz_covering_chosenWord_sideInfo_typical` は r9 で genuine outer decomposition (`AcceptFail ⊆ CoveringFail ∪ (cover-success ∩ AcceptFail)`、`measureReal_union_le`) に再構成済 = sorry-free** (`9ecffb41`)、false-as-framed fix 後 再監査 ALL-OK (`867972b2`)。残核は inner lemma に factor 済 (`sorry`+`@residual(plan:wz-binning-covering)`)。build = L0-L5 (L0 U-marginal / L1 Band-U deterministic / L2 y-projection / L3 Band-Y iid AEP / **L4 Band-Joint conditional concentration = 唯一の難所 ~150-300行** / L5 assembly)、L0-L3+L5 は now provable・L4 sorry で type-check-done。inner build → leaf を covering atom `wz_coveringFamily_of_testChannel` に consume 配線 (covering-success 分解 + joint derandomize `exists_codebook_low_avg`) + 当該 atom の stale docstring 訂正 📋

## ゴール / Approach

### Goal

親 §P3 の唯一の残 sorry である achievability の per-n covering+binning 構成を genuine closure し、WZ achievability headline `wyner_ziv_achievability` を sorryAx-free (`[propext, Classical.choice, Quot.sound]`) へ到達させる。**署名は全軸 honest 化済** (第1-5軸 closure、独立監査 all-PASS)。残 literal sorry 2 = inner `wz_covering_markov_concentration` (C2 covering-acceptance の Markov-concentration kernel、L4 Band-Joint が難所) + covering atom `wz_coveringFamily_of_testChannel` (leaf 未配線)、両方 `@residual(plan:wz-binning-covering)`。

D3 `wz_perN_covering_binning_code` (Achievability.lean:3172) は G2/A1/A2/A3 の 4 adapter を consume する sorry-free reduction (M-axis defect は Leg C.6 で解消、`@residual` は A3 から transitive 継承)。

### Approach (overall strategy / shape of solution)

解の全体像 (Leg 0-C.6 で honest 化済 + Leg E で closure):

1. **署名 honest 化 (Leg 0/C.5/C.6、DONE)** — D3/D/S6/`wz_perDelta_codes_exist` の署名を 3 段の precondition-exposure で honest 化: budget (δ-split、Leg 0)、reconciliation (`hd'_eq`/`hqf`、Leg C.5)、M-pin (`M ≤ exp(nR₁)+1`、Leg C.6)。いずれも caller `wz_coveringFamily_of_testChannel` の construction で discharge = bundling でない。
2. **error 事象 atom を実 distortion に橋渡し (Leg A/B/C、DONE)** — two-ambient WZ-joint (Leg A) + α'→α 測度変換 (Leg B) + distortion-decomposition bridge (Leg C) で closed error atom を実 `expectedBlockDistortion P_XY d` に接続。
3. **E2-only decomposition + joint derandomize (Leg D/E)** — `𝔼[actual] ≤ 𝔼[ideal] + distortionMax·Pr[E2]` (G2、DONE)。**E2 = E2b(confusion, S5b) ∪ C2(covering-acceptance, S5a)** ゆえ covering codebook を distortion **と** acceptance の両方に good に joint-derandomize (Leg E)、binning `f` は confusion に single-derandomize。squeeze で残 excess を `δ/2` に押さえ `≤ D + δ`。
4. **伝播** — 残 2 sorry (inner `wz_covering_markov_concentration` + covering atom) が消えると D3 body が transitive sorryAx を失い、上流 chain (D → S6 → `wz_perDelta_codes_exist` → `wz_goodCode_exists_of_testChannel` → headline) 経由で `wyner_ziv_achievability` sorryAx-free。

## Leg 詳細

### 完了 leg (settled、詳細 git)

- **Leg 0** (`a59e37cb`) — δ-split: `hfeas`/`hcov₁` の target を `D+δ/2` に締め `δ/2` を誤差に予約 (budget 軸 honest 化、RD `h_slack` mirror)。
- **Leg A** (`dfdf3e42`) — two-ambient WZ-joint 構成 (covering ambient `rdAmbient qStar` = S5a/C2 駆動、(U,Y) side-info ambient = S5b 駆動、共有 U-marginal で coupling、rate split `R = I(X;U) − I(Y;U)`)。regularity は `rdAmbient_*` (AchievabilityAmbientMeasure.lean) で discharge。
- **Leg B** (`02ea97d7`) — α'→α source-measure 変数変換 (iid ambient `(rdAmbient qStar).map (iidXs 0)` → `Measure.pi P_XY` の X-marginal)。
- **Leg C** (`25629b0a`) — WZ distortion-decomposition bridge (RD `source_avg_distortion_le_simpler` の bin-decoder 版)。
- **Leg C.5** (`22b64afa`) — reconciliation: `hd'_eq` (proxy `d' = 𝔼_{Y|X}[d∘qf.2]`) + `hqf` (factorizable) threading (reconciliation 軸 honest 化)。
- **Leg C.6** (`fe3d9482`/`90996ed1`) — hcov₁ M-pin: RD covering chain 結論に `M ≤ exp(nR₁)+1` 上界を露出 → hcov₁ threading → D3 body で discharge (M-axis 第3軸 honest 化)。D3 `@audit:defect` 除去 honest tier-2 復帰。

上記 6 leg は全て caller discharge の precondition-exposure (bundling でない)、ripple は Achievability.lean file-contained、独立監査 PASS。

### Leg D — E2-only decomposition glue (G2/A1/A2 DONE、A3 は Leg E へ)

**proof-log**: yes (最終組立)

**3 measures** (明示): `α' = {x:α // 0 < ∑ y P_XY.real{(x,y)}}`、`Q_XY := pmfToMeasure (fun p:α'×β ↦ P_XY.real{(p.1.1,p.2)})` (WZ block-distortion source)、`P_X' := (rdAmbient qStar).map (iidXs 0)` (covering ambient X-marginal、`hcov₁` が score)、decoder ambient `rdAmbient (wzSideInfoMarginal P_XY κ')` (E2 typicality 用)。bridge は実歪 `dα' := fun (x':α') g ↦ d x'.1 g` で score (proxy `d'` は `γ` を score 不能)。

**4-adapter split の現状**:
- **G2** `wz_expectedBlockDistortion_le_ideal_add_E2` (L2595) — E2-only generic decomp、**DONE sorry-free `@audit:ok`** (`a5e23439`)。
- **A1** (lift identity `(wzLiftSupportCode …).expectedBlockDistortion P_XY d = codeSupp.expectedBlockDistortion Q_XY dα'`) — **DONE sorry-free `@audit:ok`** (`1bb1d1ad`)。
- **A2** `wz_ideal_expectation_eq_covering` (L2879) — `𝔼_{Q_XY}[ideal blockDist under dα'] = c₁.expectedBlockDistortion P_X' d'`、**DONE sorry-free + sorryAx-free** (`84393413`、finite-sum marginalization + `hd'_eq` + Leg B)。→ `hcov₁` で `≤ (D+δ/2)+δ/4`。
- **A3** `wz_exists_binning_E2_bound` (L3022) — `Pr_{Measure.pi Q_XY}[E2] ≤ δ/(4·dMax)`、**第4軸で false-as-framed → Leg E で再設計** (下記)。

**Y-type reconciliation (維持)**: D2/S5b の `hposY` は full β で fail ゆえ **D2/S5b を `β := β'` (subtype) で instantiate** (`wzSideInfoMarginal_pos` が `hposY` discharge)。A3 内 full-β side-info への transfer は codeword law 同定でなく pure Y-marginal 一致。

### Leg E — covering-acceptance C2 再設計 (Proposal A、A3/mass DONE、残 C2 = Leg F)

**proof-log**: yes (再設計コア、再開根拠に必須)

**finding (2026-07-11、独立監査 CONFIRMED)**: A3 の E2 probability bound は E2 = E2b(confusion)∪C2(covering-acceptance) の C2 を bound する仮説を欠き **false-as-framed (第4軸)**。C2 = true covering word `c₁.decoder(trueIdx)` が side-info `Y^n` と jointly typical でない事象。`wzBinTypicalDecoder_eq_of_unique` (L1108) が回復に acceptance (joint typicality) を要求ゆえ **C2 ⊂ E2** (acceptance-failure ⇒ 非回復)。現 A3 署名は `LossyCode` bare + hcov₁ が distortion のみ供給 → C2 unbounded → **反例 = adversarial all-atypical-image covering codebook** (全 covering word が Y と atypical、hcov₁ の distortion は満たすが `dMax·Pr[E2]≈dMax > δ/4`)。**Leg D pivot の「S5a/gateway-2 dead」判定が誤り** (C2 を distortion-failure E1 と event-label 類似で混同、settled-facts OVERTURN)。

#### Approach (Proposal A、solution shape)

E2-only 分解 (G2) は維持。`E2 = E2b(confusion, S5b) ∪ C2(acceptance, Markov Lemma)` として **C2 の bound を Markov Lemma leaf (step 2) で供給**し、covering codebook を distortion **と** acceptance の両方に good に **joint-derandomize** する。5 段 (署名は pinned-ε rework `cf7d57cd` で RESOLVED、A3 fill `d1f2445a` + Leg E-mass `66417846` DONE、残 = step 2 の C2 leaf = Leg F):

1. **署名 fix (Leg C.6 同型 precondition-exposure、bundling でない)**: `hcov₁` の返り値 `c` に covering-acceptance-failure bound conjunct を追加 → A3 に対応する `hcov_accept` 仮説を追加 → upgrade 済 covering atom の construction で discharge (`wz_coveringFamily_of_testChannel:962` 単一 call-site)。**新 `*Hypothesis` predicate は作らない**。**conjunct の形は pinned-ε (first-move DEFECT の教訓、判断ログ #7)**: 半径 ε を存在量化 (`∃ ε > 0, mass ≤ tol`) すると huge-ε で jointly-typical set=全空間 → fail set ∅ → mass 0 ≤ tol が**空虚に**成立し C2 を bound しない。正しい形 = covering 構成が export する**特定 ε (goldilocks) を A3 decoder が使う同一 ε として threading** (or `∀ ε ∈ (0, ε₀]` range 形)、mass bound は Markov Lemma leaf `wz_covering_chosenWord_sideInfo_typical` (step 2、Leg F) が供給 (~~gateway-2~~ は mis-mechanization)。加えて **dα'-d reconciliation precondition** (`∀ x' g, dα' x' g = d x'.1 g` or `distortionMax dα' ≤ distortionMax d`、D3 call-site `dα':=fun x' g↦d x'.1 g` で `rfl`/`le` discharge、Leg C.5 同型) を A3 に追加 (第5軸)。**旧 S5a double-exp 形 `≤ exp(-M₁·exp(-n(I+δ)))` は不可** (M-decay ゆえ A3 の hM_ub 下で使えない、C2 は n-decay の single-word AEP — implementer の double-exp 拒否は正当だった)。
2. **covering atom C2 = Markov Lemma (r7 pivot-advisor で mis-mechanization を訂正、第6軸、判断ログ #8)**: ~~S5a+gateway-2、~40行 Fubini~~ は **誤り**。C2 = 選ばれた covering word が **相関** side-info `y` と jointly typical でない事象 (`wzCoveringAcceptFailSet` L956-965、相関-joint ambient `rdAmbient (wzSideInfoMarginal …)` 上)。S5a `wz_covering_failure_prob_le` (L1223) は single-functional covering-FAILURE `∫_x (1-slice)^M₁` = 「全 M₁ codeword が x と atypical」= covering-x 事象、gateway-2 (L144) は **独立** product side-info 上の下界 — C2 と別 measure・別 functional ゆえ **どちらも C2 を bound しない**。RD テンプレ `SupportingBounds.lean:431-483` は single-source-distortion functional (encoder が最適化する test) の joint-averaging で、C2 の y-typicality は encoder が最適化しない (encoder は y を見ない) ゆえ transfer 不能。**C2 の真の要件 = Markov Lemma**: 選ばれた word が x-typical (covering 成功) かつ (x,y) jointly typical なら (word, y) jointly typical w.h.p. = 相関-joint measure 下の conditional-typicality **concentration** (上界)。in-project 唯一の conditional-slice asset は `conditionalStronglyTypicalSlice_mass_ge` (ConditionalMethodOfTypes/Mass.lean:1274) だが **下界**・**独立** product ゆえ ingredient 止まり。**組み上がった Markov Lemma は Mathlib+codebase 双方に不在** (r7 で loogle/grep 反証済) → 別 leg F で `conditionalStronglyTypicalSlice_mass_ge` + variance/Chebyshev で self-build (~100-300行)。**named sub-lemma に isolate**: leaf `wz_covering_chosenWord_sideInfo_typical` を立て covering atom が call。r9 で leaf は genuine outer decomposition (sorry-free) 化され、残核は inner `wz_covering_markov_concentration` に factor (Leg F)。
3. **derandomize 再編**: covering `c₁` = joint derandomize (distortion+acceptance、`exists_codebook_low_avg` (`RateDistortion/AchievabilityCodebookMatchProbability.lean:138`)); binning `f` = single derandomize (confusion、`exists_pair_le_of_binning_integral_le` (`SlepianWolf/FullRateRegion/PairBound.lean:848`、private → public 化要)) を `c₁` 固定 **後**。radius double-bind (ε小→C2 / ε大→E2b) は rate gap `hsplit` で共通 ε に解消。
4. **A3 fill (DONE `d1f2445a` + Leg E-mass `66417846`/`259ecccc`)**: `hcov_accept` (C2 側) + S5b (E2b 側) を union bound で合成し `Pr[E2] ≤ Pr[C2] + Pr[E2b] ≤ δ/4` (large n、指数 → 0)。E2b の per-codeword mass は Leg E-mass `wz_source_codeword_sideInfo_mass_le` (sorry-free `@audit:ok`) が供給。**A3 sub-tree は sorryAx-free**。
5. **伝播 (残: covering atom C2 のみ)**: A3 sorry 消滅済。残 sorry 2 = Leg F の C2 leaf + covering atom。両閉じると D3 body sorry-free → headline sorryAx-free。

**headline crux 維持 = YES** (親 #9): full-support/acceptance 仮説を headline `wz_goodCode_exists_of_testChannel`/`wyner_ziv_achievability` に追加しない (support-restriction は proof-internal、acceptance は construction 内 discharge)。

**ripple**: Leg C.6 と同じ file-contained 5-decl chain (D3:3172 / D `wz_perDelta_covering_binning_eventual` / S6 `wz_perDelta_covering_binning` / `wz_perDelta_codes_exist` / `wz_coveringFamily_of_testChannel:962`) + covering atom `wz_covering_lossyCode_exists:711`。cross-file consumer 0 (機械確認済 settled-facts)。**effort 再見積り (r9 後)**: 残 = inner `wz_covering_markov_concentration` = L0-L5 (L4 Band-Joint が唯一の難所 ~150-300行、L0-L3+L5 now provable、advisor: few-sessions closable NOT wall) + leaf を covering atom へ consume 配線 (covering-success 分解 + joint-derandomize) ~1-2 dispatch。inner は `plan` atom (wall でない)。

- **消費 atom**: S5a `wz_covering_failure_prob_le:1151` / gateway-2 `wz_covering_sideInfo_mass_ge:144` / S5b `wz_codebook_confusion_expectation_le` / covering atom `wz_covering_lossyCode_exists:711` (upgrade) / joint-averaging テンプレ `SupportingBounds.lean:461-488` / `exists_codebook_low_avg` / `exists_pair_le_of_binning_integral_le` (public 化後) / G2 `wz_expectedBlockDistortion_le_ideal_add_E2:2595` / A1 / A2 `wz_ideal_expectation_eq_covering:2879`。
- **署名 rework (pinned-ε) DONE** ✅ (`cf7d57cd`/`42abbf21`、独立監査 all-PASS): `wz_coveringFamily_of_testChannel` + A3 の acceptance conjunct を pinned-ε 形に書換 (ε を `∀ ε>0` binder 化、mass を単一 ε に pin) + A3 に `hd'_link : ∀ x' g, dα' x' g = d x'.1 g` 追加、D3 で `ε := gap/6` (gap = R−(R₁−I(Y;U))) を選び `hε_conf`/`hd'_link` を linarith/rfl discharge、チェーン (covering atom / S6 / D / D3、codes_exist は inference 自動) を threading。type-check done、A2 `@audit:ok`。G2/A1/A2 は不変 (再消費)。**残 = body fill** (下 step 4-5)。
  - **body fill (r7 で再分類、判断ログ #8)**: **A3 DONE** (`d1f2445a`) = E2b/S5b と C2/hcov_accept premise を union bound、`hε_conf` が confusion 指数 `R₁−I(Y;U)+3ε−R < 0` を保証。E2b の per-codeword mass は Leg E-mass `wz_source_codeword_sideInfo_mass_le` (sorry-free `@audit:ok`) が供給 — **訂正**: この exponent bridge は `wzMutualInfoYU_eq_mutualInfo` を使わず direct pmf-level `mutualInfoPmf` 計算 (`wz_mutualInfoPmf_wzMarginalYU_eq`) を self-build (`q'` が固定 factored pmf で empirical-pmf 前提が成り立たないため、監査で逸脱 sound 確認)。**covering atom C2 = Leg F** = leaf `wz_covering_chosenWord_sideInfo_typical` は r9 で genuine outer decomposition 化済 (sorry-free)、残核を inner `wz_covering_markov_concentration` に factor → L0-L5 で self-build。
- **撤退**: `sorry + @residual(plan:wz-binning-covering)` (各 sub-lemma)。covering-acceptance を construction 無しの opaque hyp として A3 に仮定するのは **禁止 (tier-5 bundling)**。
- **依存**: Leg 0-C.6 + D の G2/A1/A2 完了後 (全 DONE)。

#### 対抗案 (reject 記録)

- **案 E (reject)**: `wzBinTypicalDecoder` を distortion-based decoder に置換 → sorry-free G2 + S3/S4 chain を破棄し、C2 が distortion tail で再出。net で悪化。
- **禁止 C**: acceptance を construction 無しの opaque hyp で A3 に仮定 = load-bearing hypothesis bundling (tier-5)。

### Leg F — C2 covering-acceptance の残核 = Markov-core (mainline、active)

> **Sub-plan**: [`wz-markov-core-plan.md`](wz-markov-core-plan.md) — conditional-AEP atom 分解 + strong-Ecov build roadmap。孫 plan が atom 状態の SoT。
>
> **2026-07-12 (Leg 12+) — Proposal A GO 確定、strong-Ecov build 進行中**: Atom C (mean-identity)/A (finite-Fubini)/B-engine (conditional-Chebyshev) は sorry-free (`ef34494a`/`95a07fa4`/`1b5be107`/`469ae6f2`)。**core `wz_covering_jointBand_markov_core` は weak typicality で FALSE-AS-FRAMED** だった (advisor + 独立 auditor が label-swap 反例で confirm、`1ddc2887` で core/outer/inner/leaf に `@audit:defect(false-statement)`) が、**gateway `wz_wsm_negLog_mean_pin_of_stronglyTypical` (`7812cfcf`、sorry-free + sorryAx-free) が strong typicality で crux を機械確認**: strong typicality → empirical type を TV で pin → `M(xb)` が `H(wsm)` に pin ⟹ label-swap が死ぬ。∴ **修正 = Proposal A** (`Ecov` のみ strong joint typicality に強化) の実行が確定路。残 = strong-Ecov build (孫 plan Atom E-H: **E+F coupled が本線** = 核 rewrite + chain 伝播、G = covering-success 下界 reopening、H = PV/closure)。**coupling 制約**: `Ecov` を core で weak→strong に変えると consume chain core→outer→inner→leaf→covering atom が一緒に変わらないとコンパイルが壊れる → E と F は 1 つの coupled 変更。headline 署名不変 (#9 crux、strength は定義由来)。詳細 → 孫 plan §Approach / `wz-facts.md`。

**proof-log**: yes (from-scratch concentration、再開根拠に必須)

**残 isolated sorry (code SoT、名は都度 `sig_view --sorry`)**: `wz_covering_jointBand_markov_core` (L5246、covering-success ∩ (x,y)-typical ∩ (u,y)-atypical ≤ tol/8)。outer `wz_covering_jointBand_concentration` (L5302) は (x,y)-AEP part-1 + core で **proved** (consume L5462)。以下 L0-L5 記述の「L4 = hard kernel」がこの core に相当。

**現状**: A3/E2b 側 CLOSED (A3 body genuine + Leg E-mass sorry-free `@audit:ok`)。C2 covering-acceptance の leaf `wz_covering_chosenWord_sideInfo_typical` は **r9 で genuine outer decomposition に再構成済 (sorry-free、`9ecffb41`)**: body = `AcceptFail ⊆ CoveringFail ∪ (covering-success ∩ AcceptFail)` を `measureReal_union_le` で閉じ、残核を isolated inner lemma `wz_covering_markov_concentration` (r9 新規、`sorry`+`@residual(plan:wz-binning-covering)`、Markov-concentration kernel) に factor。残 literal sorry 2 = inner + covering atom `wz_coveringFamily_of_testChannel` (leaf 未配線ゆえ自身の sorry)。位置 (leaf/inner/atom の line) は `scripts/sig_view.ts --sorry` で都度。

**false-as-framed fix (r9、durable lesson)**: 旧 leaf は `qStar`/`κ'` を **free/unconstrained function 引数** で持ち、constant-word 反例 (all-atypical ambient で acceptance mass≈1 > tol) で **false-as-framed**。独立 auditor が CONFIRMED (`3965ba5e`) し旧 `d2e68b10` PASS (free-param 形を tier-2 と誤認) を **overturn**。fix = **precondition-exposure (bundling でない)**: 3 regularity/consistency 仮説を leaf + inner の両方に threading:

- `hκ'_pos : ∀ x u, 0 < κ' x u` (full support)
- `hκ'_sum : ∀ x, ∑ u, κ' x u = 1` (proper conditional pmf)
- `hqStar : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)}` (qStar–κ' consistency)

covering atom `wz_coveringFamily_of_testChannel` は 3 者を **存在量化の conjunct として verbatim export** ゆえ consumer が discharge。第2の独立 confirmation audit = **ALL-OK** (`867972b2`): fixed leaf は honest tier-2、headline-safe (full-support/acceptance 仮説は headline `wz_goodCode_exists_of_testChannel`/`wyner_ziv_achievability` に leak しない)、defect 解消。

**核 de-entanglement (advisor 2026-07-12、durable)**: `jointlyTypicalSet` は `mem_jointlyTypicalSet_iff` (ChannelCoding/Basic.lean:292) で **3 つの独立 entropy-band typicality の連言** (X-typ ∧ Y-typ ∧ joint-typ) に unfold。この lemma は **rate R を持たない** (ε は固定入力)。ゆえ AcceptFail の De Morgan は 3 band-failure の union (独立 witness) になり、旧「entangled」診断は誤り。

**build scaffold = L0-L5 (`wz_covering_markov_concentration`)**:

- **L0** U-marginal identity (needs `hqStar`、~50行、easy): `marginalSnd qStar u = P_U(u)` を `wz_source_snd_marginal` の subtype-extension pattern + `hqStar` + `hκ'_sum` で。
- **L1** Band-U deterministic (~60行、easy-med): `{covering-success} ⊆ {u ∈ typicalSet …}`、mass-0、N 不要。
- **L2** y-projection (~40行、easy-med): `SRC.map (snd) = Measure.pi (per-coord snd law)` を Mathlib `Measure.pi_map_pi` で、per-coord law `∑ₓ P_XY{(x,y)} = P_Y`。
- **L3** Band-Y iid AEP (~80-120行、med): `∃N_Y, ∀ n≥N_Y, SRC.real{y_seq ∉ typicalSet …} ≤ tol/4`、ℕ-process への transport は `typicalSet_prob_ge_of_rate` (Rate.lean:220)、c 非依存。
- **L4** Band-Joint = **THE HARD KERNEL** (`sorry`+`@residual(plan:wz-binning-covering)`、~150-300行、`plan` not wall): `∃N_J, ∀ n≥N_J, ∀ M c, SRC.real({covering-success} ∩ {(u,y)-block ∉ typicalSet …}) ≤ tol/4`。**hκ'_pos/hκ'_sum/hqStar を threading 必須**。u は x-block 全体の関数 ⟹ `(u_i,y_i)` は iid でも独立でもない ⟹ plain `aep_chebyshev_bound` 不適 = conditional (method-of-types) concentration。テンプレ `conditionalStronglyTypicalSlice_mass_ge` (Mass.lean:1274) は wrong-measure/wrong-direction/wrong-typicality ⟹ drop-in 不可。**disintegration bridge (general `condDistrib` on `Measure.pi`) は不要だが理由は「回避」でなく off-path** (child SoT で訂正): SRC = `Measure.pi (pmfToMeasure Src)` ゆえ x-block factor-out は `Measure.pi_pi` + `pmfToMeasure` atomicity の**有限 Fubini**、実装者の condDistrib 0-hit は general machinery 側で正しいが critical path 外。真の bulk は conditional Chebyshev (`IndepFun.variance_sum`、**IdentDistrib 不要**)。→ 詳細/atom 分解 (mean-identity warm-up → finite Fubini → conditional Chebyshev → 組立) は子 [`wz-markov-core-plan.md`](wz-markov-core-plan.md)。
- **L5** assembly (~40行、easy): `N := max N_Y N_J`、`mem_jointlyTypicalSet_iff` + De Morgan、`measureReal_union_le` で 0 + tol/4 + tol/4 = tol/2。

**verdict (advisor 2026-07-12)**: **few-sessions closable、NOT a wall**。L4 が唯一の real difficulty、L0-L3+L5 は now provable、L4 sorry で即 type-check-done。

**2 flag (non-blocking、次に covering atom を touch する際に処理)**:

- **stale docstring**: covering atom `wz_coveringFamily_of_testChannel` CODE docstring が旧「S5a/gateway-2 Fubini derandomize」機構を記述 = STALE。leaf consume 配線時に訂正 (code がタグの SoT、本 plan からは fix せず flag のみ)。
- **factor-2 tolerance mismatch**: A3 の `hcov_accept` は `≤ δ/2/(8·(distortionMax d+1))`、covering atom は `≤ δ/(8·(distortionMax d+1))` を export = harmless (両者 C2→0 由来、「任意固定正 tol に eventually ≤」leaf/inner が discharge、D3 が同 ε を threading)。

**撤退**: `sorry + @residual(plan:wz-binning-covering)` (inner / covering atom 各)。

## 撤退ライン / honesty (集約)

- **撤退口は `sorry + @residual(plan:wz-binning-covering)` のみ** (class は **`plan` 固定**、slug = 本 plan filename stem)。WZ の gap は Mathlib gap でなく in-project atom の未実装 (親 §200、inventory §8) ゆえ **`wall` は使わない**。
- **bundling 禁止**: covering 下界 / covering-acceptance / error 確率 / decoder-correctness を `*Hypothesis`/`*Reduction`/`IsXxxClaim` predicate に bundle しない。`Prop := True` slot 禁止、退化定義悪用禁止。regularity hyp (full-support / `IsProbabilityMeasure` / 可測性 / `iIndepFun` / `Nonempty` / uniform message) は precondition で OK。
- **precondition-exposure は bundling でない**: hcov₁ への acceptance-failure bound conjunct 追加 (Leg E) は、Leg 0/C.5/C.6 と同型で caller construction が discharge する派生 precondition の露出。core を仮説に encode しない (S5a/gateway-2 の指数 → 0 は実解析 work)。
- **A2 監査 pending**: A2 `wz_ideal_expectation_eq_covering` は sorry-free だが独立監査未実施。Leg E closure 時に A3 と併せ comprehensive 独立 honesty-auditor 1 pass。
- **headline signature 不変 (crux、親 #9 継承)**: `wz_goodCode_exists_of_testChannel` / `wyner_ziv_achievability` に full-support/acceptance 仮説を追加しない。

## settled-facts (minimal、再導出可能なものは都度 `#print axioms` / `rg`)

- **E1 (covering-distortion-failure `{ideal blockDist > P}`) は D3 で squeeze 不能 → E2-only decomposition が正しい shape (pivot 2026-07-11、維持)**: `hcov₁` は **expected distortion** を供給し covering-typicality でない。fixed `c₁` に対し `Pr[E1] ≤ 𝔼[ideal]/P > 1` (Markov) ゆえ E1→0 不可。∴ `𝔼[actual] ≤ 𝔼[ideal] + distortionMax·Pr[E2]` (G2 `wz_expectedBlockDistortion_le_ideal_add_E2:2595` `@audit:ok`)。confidence: human-judgment (Markov 反証)。
- **【C2 mechanism = correlated-joint conditional concentration、S5a/gateway-2 は C2 を bound しない (r7→r9 訂正)】**: C2 = 選ばれた covering word が **相関** side-info Y と非 jointly-typical (相関-joint ambient 上、`u = c.decoder(c.encoder x)` は source x の関数)。S5a (`wz_covering_failure_prob_le`) は covering-FAILURE (all-codeword-atypical-with-x)・gateway-2 (`wz_covering_sideInfo_mass_ge`) は **独立** product 下界 ゆえ **別 measure・別 functional で C2 を bound しない** (旧「S5a/gateway-2 ~40行 Fubini で bound」は mis-mechanization)。真の要件 = correlated-joint 下の conditional-typicality concentration 上界、in-project の `conditionalStronglyTypicalSlice_mass_ge` (Mass.lean:1274) は下界・独立 product で ingredient 止まり → Leg F の inner `wz_covering_markov_concentration` を L0-L5 で self-build。**leaf の free-param 形 (qStar/κ' unconstrained) は constant-word 反例で false-as-framed だった** (独立 auditor CONFIRMED `3965ba5e`、旧 `d2e68b10` PASS overturn) → 3 regularity (`hκ'_pos`/`hκ'_sum`/`hqStar`) threading で TRUE-as-framed 化・再監査 ALL-OK (`867972b2`、headline-safe)。dead なのは E1 (distortion-failure) のみ。**durable lesson**: residual leaf を isolate する前に消費 site の ACTUAL measure/coupling を verbatim 確認 — 独立-product 簡約 (advisor 初回提案) も free-param 化 も leaf を silently 偽にしうる。confidence: machine (独立 auditor 2 pass + refutation)。詳細 → Leg F。
- **署名 fix ripple = Achievability.lean file-contained**: Leg 0/C.5/C.6/E の precondition threading は 5-decl chain (`wz_coveringFamily_of_testChannel:962` / D `wz_perDelta_covering_binning_eventual` / D3 `wz_perN_covering_binning_code:3172` / S6 `wz_perDelta_covering_binning` / `wz_perDelta_codes_exist`) + covering atom `wz_covering_lossyCode_exists:711` に限局、全て Achievability.lean 内参照 (cross-file consumer 0)。headline 署名不変 (親 #9 crux)。confidence: machine (`rg -l` 確認)。

(budget 軸 = Leg 0 / reconciliation 軸 = Leg C.5 / M-axis 第3軸 = Leg C.6 は解消済 = 再導出可能ゆえ settled-facts から除去、git 履歴保持。再導出可能なもの = sorryAx-free / decl 存在 / sorry の有無 はキャッシュしない、`#print axioms` / `scripts/sig_view.ts --sorry` で都度。)

## 判断ログ

append-only。決着済 entry は削除 (git が履歴)、active のみ残す。≤ 10 entry。

2. **two-ambient subtlety (Leg A DONE、親 §B4/#10 継承、structural、Leg E も依拠)**: TWO ambients — covering ambient `rdAmbient qStar` (S5a/C2 駆動) と (U,Y) side-info ambient (S5b/E2b 駆動) は同一 3-var `q'` の 2 marginal、共有 U-marginal で rate split `R = I(X;U) − I(Y;U)` 一貫。regularity は `rdAmbient_*` で discharge (bundle しない)。
3. **E2 = E2b(confusion) ∪ C2(acceptance) が WZ の真の核 (親 #10 継承、active)**: WZ を SW と分ける核は codebook 限定 confusion E2b (S5b `wz_codebook_confusion_expectation_le`、sorry-free)、acceptance-failure C2 は `wzBinTypicalDecoder_eq_of_unique` が回復に acceptance を要求ゆえ C2 ⊂ E2。**E2b 側は CLOSED** (A3 body genuine + Leg E-mass `wz_source_codeword_sideInfo_mass_le` sorry-free `@audit:ok`)。**C2 側の残核 = inner `wz_covering_markov_concentration` (correlated-joint conditional concentration) = Leg F** (S5a/gateway-2 ではない — 旧「S5a/gateway-2 で C2 を bound」は mis-mechanization、S5a/gateway-2 は covering/独立-product 側で C2 = 相関-joint acceptance を bound しない、#8 参照)。leaf `wz_covering_chosenWord_sideInfo_typical` は r9 で genuine outer decomposition 化済 (sorry-free)。dead なのは E1 (distortion-failure) のみ。
6. **under-hyp トラップ family (第3-4軸、settled、durable lesson、親 #11 参照)**: M-axis (第3軸、`M ≤ exp(nR₁)+1` pin、Leg C.6) + covering-acceptance C2 (第4軸) は honest 化済。**durable lesson**: error-event atom を event-name の類似で dead-judge するな (Leg D が S5a を「E1 と同種」と誤判定)、dead 判定は **conclusion の集合所属述語**で検証。under-hyp は明示 param + ∃-witness(M) + **conclusion の sub-event 内 (C2 ⊂ E2)** の 3 所に潜む (family トラップ、親 #11 が ledger)。
7. **退化 binder check (第5軸、settled=RESOLVED `cf7d57cd`、durable lesson、親 #12 参照)**: Leg E first-move 署名は free-∃ε vacuous + dα'-d scaling gap の 2 flaw で DEFECT だったが pinned-ε rework で RESOLVED (退化 binder table 全 BLOCKED)。**durable lesson**: (i) WZ 署名-fix を closed と宣言する前に全 free binder (ε/dα'/M/d') を退化極値で instantiate する check を必須化。(ii) 2 sub-lemma が opposite monotone 方向に押す共有 param は片方内で量化不可 (`∃` は片極で vacuous、`∀`-range は他極で偽) — 最近共通祖先 (D3) で構造 gap (rate margin) から選ぶ explicit shared input 化が唯一 honest。
8. **Leg F = C2 covering-acceptance residual = inner `wz_covering_markov_concentration` (r7 pivot-advisor → r9 false-as-framed overturn + fix、active、本線)**: A3/E2b 側 CLOSED (A3 genuine `d1f2445a` + Leg E-mass `@audit:ok` `66417846`/`259ecccc`、exponent bridge は direct pmf-level `mutualInfoPmf` を self-build)。C2 側 = 真の blocker。**r9 の 2 訂正**: (a) 旧 leaf `wz_covering_chosenWord_sideInfo_typical` は `qStar`/`κ'` を free/unconstrained で持ち constant-word 反例で **false-as-framed** (独立 auditor CONFIRMED `3965ba5e`、旧 `d2e68b10` PASS = free-param 形を tier-2 と誤認していたのを overturn) → full-support/proper-pmf/qStar-κ' consistency の 3 regularity (`hκ'_pos`/`hκ'_sum`/`hqStar`) を leaf+inner に threading (precondition-exposure、bundling でない、covering atom が 3 者を存在 conjunct として verbatim export ゆえ discharge) で TRUE-as-framed 化、再監査 ALL-OK (`867972b2`、headline-safe)。(b) leaf body を **genuine outer decomposition** に再構成 (`9ecffb41`、sorry-free): `AcceptFail ⊆ CoveringFail ∪ (cover-success ∩ AcceptFail)` を `measureReal_union_le` で閉じ、残核を isolated inner `wz_covering_markov_concentration` に factor。**inner build = L0-L5 scaffold (詳細 → Leg F)**: `jointlyTypicalSet` は `mem_jointlyTypicalSet_iff` で 3 独立 band-typicality に unfold (rate R なし) ゆえ De Morgan で 3 band-failure union — 旧「entangled」診断は誤り。L4 Band-Joint conditional concentration が唯一の難所 (~150-300行、u が x-block 全体の関数 ⟹ 非iid・非独立 ⟹ conditional method-of-types、`conditionalStronglyTypicalSlice_mass_ge` は wrong-measure/direction/typicality で drop-in 不可)、L0-L3+L5 now provable・L4 sorry で type-check-done。advisor verdict = **few-sessions closable、NOT a wall**。**mainline (B+D)**: inner を L0-L5 で build → leaf を covering atom `wz_coveringFamily_of_testChannel` に consume 配線 (covering-success 分解 + joint-derandomize `exists_codebook_low_avg`) + 当該 atom の stale docstring 訂正。両 sorry closing で headline sorryAx-free。**教訓 (durable、#6 family 第3実例、親 #12 が ledger)**: residual leaf を isolate する前に消費 site の ACTUAL measure/coupling を verbatim 確認 — 独立-product 簡約 も free-param 化 も leaf を silently 偽にしうる、event 名の一致を mechanism の一致と取り違えるな。
