# Wyner–Ziv achievability: D3 binning + covering closure サブ計画

> **Parent**: [`wyner-ziv-main-plan.md`](wyner-ziv-main-plan.md) §P3 D3 split-out

**Status**: ACTIVE 🚧 — 署名は全軸 honest (第1-5軸 closure、独立監査 all-PASS `cf7d57cd`/`42abbf21`)。**残 literal sorry 2 の性質が r7 pivot-advisor で再分類** (第6軸、下記 判断ログ #8): 2 sorry は同一 blocker でなく非対称。**(A3 `wz_exists_binning_E2_bound` L3138 = tractable NOW** — C2 mass 下界を*仮説* `hcov_accept` で取り、E2b confusion を S5b(L1344 `@audit:ok`)+D2(L1897 `@audit:ok`)+β'→β transfer で bound、assets 全て存在)。**covering atom `wz_coveringFamily_of_testChannel` L1024 の C2 conjunct = 真の blocker、MARKOV LEMMA を要し Mathlib+codebase 双方に genuinely 不在**。旧計画の「S5a+gateway-2、~40行 Fubini、wall-risk LOW」は **mis-mechanization** (S5a/gateway-2 は covering/独立-product 側、C2 は相関-joint acceptance の concentration = 別 measure・別 functional、event-label 混同 #6 の第3実例)。C2 closure = `conditionalStronglyTypicalSlice_mass_ge` (下界 ingredient) 上に variance/Chebyshev で組む in-project Markov Lemma (~100-300行、別 leg)。**A2 `wz_ideal_expectation_eq_covering` `@audit:ok`**。両 sorry `@residual(plan:wz-binning-covering)`。**次 = A3 fill + C2 を named Markov sub-lemma に isolate**。**Leg C.6/C.5/D G2/A1/A2 + Leg 0/A/B/C DONE**。

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
- [ ] Leg E-A3 fill (**active 本線、tractable**) — A3 `wz_exists_binning_E2_bound` を C2-as-hypothesis 形で closure: {decoder≠true}⊆C2∪E2b (`wzBinTypicalDecoder_eq_of_unique` 対偶)、C2 は `hcov_accept` premise、E2b は S5b(L1344)+D2(L1897)+β'→β transfer 📋
- [ ] Leg F — covering atom C2 = **Markov Lemma leg** (新規、~100-300行、multi-leg): C2 を named sub-lemma `wz_covering_chosenWord_sideInfo_typical` に isolate → `conditionalStronglyTypicalSlice_mass_ge` 上に相関-joint concentration を self-build。gateway-atom-first で壁/tractable 判定 📋

## ゴール / Approach

### Goal

親 §P3 の唯一の残 sorry である achievability の per-n covering+binning 構成を genuine closure し、WZ achievability headline `wyner_ziv_achievability` を sorryAx-free (`[propext, Classical.choice, Quot.sound]`) へ到達させる。**署名は全軸 honest 化済** (第1-5軸 closure、独立監査 all-PASS)。残 literal sorry 2 = 解析 body fill のみ (covering atom acceptance Fubini + A3 E2b confusion 指数)、両方 `@residual(plan:wz-binning-covering)`。

D3 `wz_perN_covering_binning_code` (Achievability.lean:3172) は G2/A1/A2/A3 の 4 adapter を consume する sorry-free reduction (M-axis defect は Leg C.6 で解消、`@residual` は A3 から transitive 継承)。

### Approach (overall strategy / shape of solution)

解の全体像 (Leg 0-C.6 で honest 化済 + Leg E で closure):

1. **署名 honest 化 (Leg 0/C.5/C.6、DONE)** — D3/D/S6/`wz_perDelta_codes_exist` の署名を 3 段の precondition-exposure で honest 化: budget (δ-split、Leg 0)、reconciliation (`hd'_eq`/`hqf`、Leg C.5)、M-pin (`M ≤ exp(nR₁)+1`、Leg C.6)。いずれも caller `wz_coveringFamily_of_testChannel` の construction で discharge = bundling でない。
2. **error 事象 atom を実 distortion に橋渡し (Leg A/B/C、DONE)** — two-ambient WZ-joint (Leg A) + α'→α 測度変換 (Leg B) + distortion-decomposition bridge (Leg C) で closed error atom を実 `expectedBlockDistortion P_XY d` に接続。
3. **E2-only decomposition + joint derandomize (Leg D/E)** — `𝔼[actual] ≤ 𝔼[ideal] + distortionMax·Pr[E2]` (G2、DONE)。**E2 = E2b(confusion, S5b) ∪ C2(covering-acceptance, S5a)** ゆえ covering codebook を distortion **と** acceptance の両方に good に joint-derandomize (Leg E)、binning `f` は confusion に single-derandomize。squeeze で残 excess を `δ/2` に押さえ `≤ D + δ`。
4. **伝播** — A3 の sorry が消えると D3 body sorry-free → 上流 chain (D → S6 → `wz_perDelta_codes_exist` → `wz_goodCode_exists_of_testChannel` → headline) が transitive sorryAx を失い `wyner_ziv_achievability` sorryAx-free。

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

### Leg E — covering-acceptance C2 再設計 (Proposal A、active 本線)

**proof-log**: yes (再設計コア、再開根拠に必須)

**finding (2026-07-11、独立監査 CONFIRMED)**: A3 の E2 probability bound は E2 = E2b(confusion)∪C2(covering-acceptance) の C2 を bound する仮説を欠き **false-as-framed (第4軸)**。C2 = true covering word `c₁.decoder(trueIdx)` が side-info `Y^n` と jointly typical でない事象。`wzBinTypicalDecoder_eq_of_unique` (L1108) が回復に acceptance (joint typicality) を要求ゆえ **C2 ⊂ E2** (acceptance-failure ⇒ 非回復)。現 A3 署名は `LossyCode` bare + hcov₁ が distortion のみ供給 → C2 unbounded → **反例 = adversarial all-atypical-image covering codebook** (全 covering word が Y と atypical、hcov₁ の distortion は満たすが `dMax·Pr[E2]≈dMax > δ/4`)。**Leg D pivot の「S5a/gateway-2 dead」判定が誤り** (C2 を distortion-failure E1 と event-label 類似で混同、settled-facts OVERTURN)。

#### Approach (Proposal A、solution shape)

E2-only 分解 (G2) は維持。`E2 = E2b(confusion, S5b) ∪ C2(acceptance, S5a)` として **S5a/gateway-2 を復活**させ、covering codebook を distortion **と** acceptance の両方に good に **joint-derandomize** する。5 段:

1. **署名 fix (Leg C.6 同型 precondition-exposure、bundling でない)**: `hcov₁` の返り値 `c` に covering-acceptance-failure bound conjunct を追加 → A3 に対応する `hcov_accept` 仮説を追加 → upgrade 済 covering atom の construction で discharge (`wz_coveringFamily_of_testChannel:962` 単一 call-site)。**新 `*Hypothesis` predicate は作らない**。**conjunct の形は pinned-ε (first-move DEFECT の教訓、判断ログ #7)**: 半径 ε を存在量化 (`∃ ε > 0, mass ≤ tol`) すると huge-ε で jointly-typical set=全空間 → fail set ∅ → mass 0 ≤ tol が**空虚に**成立し C2 を bound しない。正しい形 = covering 構成が export する**特定 ε (goldilocks) を A3 decoder が使う同一 ε として threading** (or `∀ ε ∈ (0, ε₀]` range 形)、mass bound は gateway-2 `wz_covering_sideInfo_mass_ge:144` 供給。加えて **dα'-d reconciliation precondition** (`∀ x' g, dα' x' g = d x'.1 g` or `distortionMax dα' ≤ distortionMax d`、D3 call-site `dα':=fun x' g↦d x'.1 g` で `rfl`/`le` discharge、Leg C.5 同型) を A3 に追加 (第5軸)。**旧 S5a double-exp 形 `≤ exp(-M₁·exp(-n(I+δ)))` は不可** (M-decay ゆえ A3 の hM_ub 下で使えない、C2 は n-decay の single-word AEP — implementer の double-exp 拒否は正当だった)。
2. **covering atom C2 = Markov Lemma (r7 pivot-advisor で mis-mechanization を訂正、第6軸、判断ログ #8)**: ~~S5a+gateway-2、~40行 Fubini~~ は **誤り**。C2 = 選ばれた covering word が **相関** side-info `y` と jointly typical でない事象 (`wzCoveringAcceptFailSet` L956-965、相関-joint ambient `rdAmbient (wzSideInfoMarginal …)` 上)。S5a `wz_covering_failure_prob_le` (L1223) は single-functional covering-FAILURE `∫_x (1-slice)^M₁` = 「全 M₁ codeword が x と atypical」= covering-x 事象、gateway-2 (L144) は **独立** product side-info 上の下界 — C2 と別 measure・別 functional ゆえ **どちらも C2 を bound しない**。RD テンプレ `SupportingBounds.lean:431-483` は single-source-distortion functional (encoder が最適化する test) の joint-averaging で、C2 の y-typicality は encoder が最適化しない (encoder は y を見ない) ゆえ transfer 不能。**C2 の真の要件 = Markov Lemma**: 選ばれた word が x-typical (covering 成功) かつ (x,y) jointly typical なら (word, y) jointly typical w.h.p. = 相関-joint measure 下の conditional-typicality **concentration** (上界)。in-project 唯一の conditional-slice asset は `conditionalStronglyTypicalSlice_mass_ge` (ConditionalMethodOfTypes/Mass.lean:1274) だが **下界**・**独立** product ゆえ ingredient 止まり。**組み上がった Markov Lemma は Mathlib+codebase 双方に不在** (r7 で loogle/grep 反証済) → 別 leg F で `conditionalStronglyTypicalSlice_mass_ge` + variance/Chebyshev で self-build (~100-300行)。**named sub-lemma に isolate**: `wz_covering_chosenWord_sideInfo_typical` (C2 mass 上界を主張、body `sorry+@residual(plan:…)`) を立て、covering atom が call。
3. **derandomize 再編**: covering `c₁` = joint derandomize (distortion+acceptance、`exists_codebook_low_avg` (`RateDistortion/AchievabilityCodebookMatchProbability.lean:138`)); binning `f` = single derandomize (confusion、`exists_pair_le_of_binning_integral_le` (`SlepianWolf/FullRateRegion/PairBound.lean:848`、private → public 化要)) を `c₁` 固定 **後**。radius double-bind (ε小→C2 / ε大→E2b) は rate gap `hsplit` で共通 ε に解消。
4. **A3 fill**: `hcov_accept` (C2 側) + S5b (E2b 側) を union bound で合成し `Pr[E2] ≤ Pr[C2] + Pr[E2b] ≤ δ/(4·dMax)` (large n、S5a/S5b の指数 → 0)。
5. **伝播**: A3 sorry 消滅 → D3 body sorry-free → headline sorryAx-free。

**headline crux 維持 = YES** (親 #9): full-support/acceptance 仮説を headline `wz_goodCode_exists_of_testChannel`/`wyner_ziv_achievability` に追加しない (support-restriction は proof-internal、acceptance は construction 内 discharge)。

**ripple**: Leg C.6 と同じ file-contained 5-decl chain (D3:3172 / D `wz_perDelta_covering_binning_eventual` / S6 `wz_perDelta_covering_binning` / `wz_perDelta_codes_exist` / `wz_coveringFamily_of_testChannel:962`) + covering atom `wz_covering_lossyCode_exists:711`。cross-file consumer 0 (機械確認済 settled-facts)。**effort 再見積り (r7)**: A3 fill ~1-2 dispatch (assets 存在) + covering atom C2 = Markov Lemma leg F ~100-300行/multi-leg (self-build) + joint-derandomize wiring ~1-2 dispatch。C2 は `plan` atom (wall でない、in-project 未実装)。

- **消費 atom**: S5a `wz_covering_failure_prob_le:1151` / gateway-2 `wz_covering_sideInfo_mass_ge:144` / S5b `wz_codebook_confusion_expectation_le` / covering atom `wz_covering_lossyCode_exists:711` (upgrade) / joint-averaging テンプレ `SupportingBounds.lean:461-488` / `exists_codebook_low_avg` / `exists_pair_le_of_binning_integral_le` (public 化後) / G2 `wz_expectedBlockDistortion_le_ideal_add_E2:2595` / A1 / A2 `wz_ideal_expectation_eq_covering:2879`。
- **署名 rework (pinned-ε) DONE** ✅ (`cf7d57cd`/`42abbf21`、独立監査 all-PASS): `wz_coveringFamily_of_testChannel` + A3 の acceptance conjunct を pinned-ε 形に書換 (ε を `∀ ε>0` binder 化、mass を単一 ε に pin) + A3 に `hd'_link : ∀ x' g, dα' x' g = d x'.1 g` 追加、D3 で `ε := gap/6` (gap = R−(R₁−I(Y;U))) を選び `hε_conf`/`hd'_link` を linarith/rfl discharge、チェーン (covering atom / S6 / D / D3、codes_exist は inference 自動) を threading。type-check done、A2 `@audit:ok`。G2/A1/A2 は不変 (再消費)。**残 = body fill** (下 step 4-5)。
  - **body fill (r7 で再分類、判断ログ #8)**: **A3 (active、tractable)** = E2b/S5b (D2 `hI_YU`+`wzMutualInfoYU_eq_mutualInfo` bridge) と C2/hcov_accept premise を union bound、`hε_conf` が confusion 指数 `R₁−I(Y;U)+3ε−R < 0` を保証。**covering atom C2 = leg F (Markov Lemma、~40行 Fubini は誤り)** = `conditionalStronglyTypicalSlice_mass_ge` 上に相関-joint concentration を self-build、named sub-lemma に isolate。
- **撤退**: `sorry + @residual(plan:wz-binning-covering)` (各 sub-lemma)。covering-acceptance を construction 無しの opaque hyp として A3 に仮定するのは **禁止 (tier-5 bundling)**。
- **依存**: Leg 0-C.6 + D の G2/A1/A2 完了後 (全 DONE)。

#### 対抗案 (reject 記録)

- **案 E (reject)**: `wzBinTypicalDecoder` を distortion-based decoder に置換 → sorry-free G2 + S3/S4 chain を破棄し、C2 が distortion tail で再出。net で悪化。
- **禁止 C**: acceptance を construction 無しの opaque hyp で A3 に仮定 = load-bearing hypothesis bundling (tier-5)。

## 撤退ライン / honesty (集約)

- **撤退口は `sorry + @residual(plan:wz-binning-covering)` のみ** (class は **`plan` 固定**、slug = 本 plan filename stem)。WZ の gap は Mathlib gap でなく in-project atom の未実装 (親 §200、inventory §8) ゆえ **`wall` は使わない**。
- **bundling 禁止**: covering 下界 / covering-acceptance / error 確率 / decoder-correctness を `*Hypothesis`/`*Reduction`/`IsXxxClaim` predicate に bundle しない。`Prop := True` slot 禁止、退化定義悪用禁止。regularity hyp (full-support / `IsProbabilityMeasure` / 可測性 / `iIndepFun` / `Nonempty` / uniform message) は precondition で OK。
- **precondition-exposure は bundling でない**: hcov₁ への acceptance-failure bound conjunct 追加 (Leg E) は、Leg 0/C.5/C.6 と同型で caller construction が discharge する派生 precondition の露出。core を仮説に encode しない (S5a/gateway-2 の指数 → 0 は実解析 work)。
- **A2 監査 pending**: A2 `wz_ideal_expectation_eq_covering` は sorry-free だが独立監査未実施。Leg E closure 時に A3 と併せ comprehensive 独立 honesty-auditor 1 pass。
- **headline signature 不変 (crux、親 #9 継承)**: `wz_goodCode_exists_of_testChannel` / `wyner_ziv_achievability` に full-support/acceptance 仮説を追加しない。

## settled-facts (minimal、再導出可能なものは都度 `#print axioms` / `rg`)

- **E1 (covering-distortion-failure `{ideal blockDist > P}`) は D3 で squeeze 不能 → E2-only decomposition が正しい shape (pivot 2026-07-11、維持)**: `hcov₁` は **expected distortion** を供給し covering-typicality でない。fixed `c₁` に対し `Pr[E1] ≤ 𝔼[ideal]/P > 1` (Markov) ゆえ E1→0 不可。∴ `𝔼[actual] ≤ 𝔼[ideal] + distortionMax·Pr[E2]` (G2 `wz_expectedBlockDistortion_le_ideal_add_E2:2595` `@audit:ok`)。confidence: human-judgment (Markov 反証)。
- **【C2 mechanism = Markov Lemma、S5a/gateway-2 は C2 を bound しない (r7 訂正 2026-07-12、第6軸)】**: 履歴 = 3 段の event-label 混同。Leg D「S5a/gateway-2 dead」→ Leg E 第4軸「S5a/gateway-2 live で C2 を ~40行 Fubini で bound」→ **r7 で後者も誤りと判明**。正しくは: (i) C2 ⊂ E2 は正 (`wzBinTypicalDecoder_eq_of_unique:1180` が回復に acceptance を要求)、A3 は C2 を*仮説*で取り tractable。(ii) だが C2 = 選ばれた covering word が**相関** side-info Y と非 jointly-typical (相関-joint ambient 上)、S5a (`wz_covering_failure_prob_le:1223`) は covering-FAILURE (all-codeword-atypical-with-x、covering-x 事象)・gateway-2 (`:144`) は**独立** product 下界 ゆえ **別 measure・別 functional で C2 を bound しない**。(iii) C2 の真の要件 = **Markov Lemma** (相関-joint 下の conditional-typicality concentration 上界)、in-project の `conditionalStronglyTypicalSlice_mass_ge` (Mass.lean:1274) は下界・独立 product で ingredient 止まり、**組上済 Markov Lemma は不在** → leg F で self-build。confidence: **machine** (r7 pivot-advisor + orchestrator 独立 refutation: C2 def L956-965 相関-joint 確認、A3 L3153-3158 が C2 を premise 化 確認、loogle/grep で Markov Lemma 0-hit 確認)。dead なのは E1 (distortion-failure) のみ (下記維持)。
- **署名 fix ripple = Achievability.lean file-contained**: Leg 0/C.5/C.6/E の precondition threading は 5-decl chain (`wz_coveringFamily_of_testChannel:962` / D `wz_perDelta_covering_binning_eventual` / D3 `wz_perN_covering_binning_code:3172` / S6 `wz_perDelta_covering_binning` / `wz_perDelta_codes_exist`) + covering atom `wz_covering_lossyCode_exists:711` に限局、全て Achievability.lean 内参照 (cross-file consumer 0)。headline 署名不変 (親 #9 crux)。confidence: machine (`rg -l` 確認)。

(budget 軸 = Leg 0 / reconciliation 軸 = Leg C.5 / M-axis 第3軸 = Leg C.6 は解消済 = 再導出可能ゆえ settled-facts から除去、git 履歴保持。再導出可能なもの = sorryAx-free / decl 存在 / sorry の有無 はキャッシュしない、`#print axioms` / `scripts/sig_view.ts --sorry` で都度。)

## 判断ログ

append-only。決着済 entry は削除 (git が履歴)、active のみ残す。≤ 10 entry。

2. **two-ambient subtlety (Leg A DONE、親 §B4/#10 継承、structural、Leg E も依拠)**: TWO ambients — covering ambient `rdAmbient qStar` (S5a/C2 駆動) と (U,Y) side-info ambient (S5b/E2b 駆動) は同一 3-var `q'` の 2 marginal、共有 U-marginal で rate split `R = I(X;U) − I(Y;U)` 一貫。regularity は `rdAmbient_*` で discharge (bundle しない)。
3. **E2 = E2b(confusion) ∪ C2(acceptance) が WZ の真の核 (親 #10 継承 + 第4軸で細分、active)**: WZ を SW と分ける核は codebook 限定 confusion E2b (S5b `wz_codebook_confusion_expectation_le`、CLOSED sorry-free)。**pivot 2026-07-11 では「D3 は E1-free = E2 唯一 error、S5a/gateway-2 dead」としたが第4軸で撤回** (settled-facts OVERTURN): E2 は E2b **と** covering-acceptance failure C2 の union (acceptance 要求 `wzBinTypicalDecoder_eq_of_unique:1108` ゆえ C2 ⊂ E2)、C2 の bound を S5a (L1151) + gateway-2 (L144) が供給 = **S5a/gateway-2 は live**。dead なのは E1 (distortion-failure) のみ。Leg E が E2b (S5b) + C2 (S5a) を両方消費。
4. **M-axis (第3軸) 解消済 (Leg C.6、settled)**: `hcov₁` に `M ≤ exp(nR₁)+1` 上界を pin (Leg 0/C.5 同型 precondition tightening)、D3 body で discharge → D3 `@audit:defect` 除去 honest tier-2 復帰 (`fe3d9482`/`90996ed1`、独立監査 all-PASS)。教訓 (under-hyp は明示 param + ∃-witness の両方に潜む) は下記 #6 第4軸 entry で sub-event まで一般化。
5. **Leg D E2-only 分解は正しい (G2/A1/A2 DONE) が A3 が第4軸で false-as-framed → Leg E (active、本線、2026-07-11)**: E2-only decomp G2 (`wz_expectedBlockDistortion_le_ideal_add_E2:2595` `@audit:ok`) は正しく維持、A1 (lift identity) / A2 (`wz_ideal_expectation_eq_covering:2879`、finite-sum marginalization、`84393413`) も sorry-free。だが A3 (E2 probability bound) は E2 = E2b∪C2 の C2 (covering-acceptance) を bound する仮説を欠き false-as-framed (第4軸)。**Leg D pivot の「S5a/gateway-2 dead」判定が誤りだった** (C2 を E1 と混同、上記 #3/settled-facts)。→ Leg E で S5a/gateway-2 を復活 + covering codebook joint-derandomize。A2/A3 の comprehensive 独立監査は Leg E closure 時に実施。
6. **第4軸 = covering-acceptance C2 発見 → Leg E 再設計 (Proposal A、active、本線、2026-07-11、独立監査 CONFIRMED)**: A3 の残 sorry は E2 = E2b(confusion)∪C2(acceptance) の C2 を bound する仮説を欠き false-as-framed。C2 = true covering word が side-info Y と jointly typical でない事象、`wzBinTypicalDecoder_eq_of_unique:1108` が回復に acceptance を要求ゆえ C2 ⊂ E2。現 A3 署名は `LossyCode` bare + hcov₁ が distortion のみ供給 → C2 unbounded → 反例 (adversarial all-atypical-image codebook) で `dMax·Pr[E2]≈dMax > δ/4`。**FIX = Leg E (Proposal A)**: E2-only 分解 G2 は維持、S5a (L1151) + gateway-2 (L144) を復活させ C2 を bound、covering codebook を distortion+acceptance に joint-derandomize (`SupportingBounds.lean:461-488` の既存 joint-averaging テンプレ流用、~40 行 Fubini plumbing)。署名 fix = hcov₁ に acceptance-failure bound conjunct 追加 + A3 に `hcov_accept` 追加 (Leg C.6 同型 precondition-exposure、bundling でない、新 `*Hypothesis` predicate は作らない)。**教訓 (proof-pivot-advisor)**: error-event atom を event-name の類似で dead-judge するな (Leg D が S5a を「E1 と同種」と誤判定)。dead 判定は informal な事象ラベルでなく **conclusion の集合所属述語**で検証。under-hyp 軸は明示 param + ∃-witness(M) + **conclusion の sub-event 内 (C2 ⊂ E2)** にも潜む (第4軸、#11 family トラップ 4 度目)。**署名は RESOLVED** (pinned-ε rework `cf7d57cd`、独立監査 all-PASS): C2 を pinned-ε acceptance conjunct で*仮説*化、署名 honest tier-2。**但し closure MECHANISM (「S5a+gateway-2 の ~40行 Fubini で C2 を bound」) は r7 で誤りと判明** → #8 参照 (C2 = Markov Lemma、S5a/gateway-2 は covering-side で C2 を bound せず)。
7. **第5軸 = dα'-d scaling 発見 + Leg E first-move 署名が DEFECT (2026-07-12、独立監査 CONFIRMED、`b5b22385`→notes `d71b9dfb`、active)**: Leg E first move (acceptance thread の signature ripple) は 2 つの tier-5 flaw で C2 軸を閉じられず `@audit:defect(false-statement)` 維持 (tier-2 降格せず)。(i) **degenerate `∃ ε`**: `hcov_accept = ∃ ε>0, mass(wzCoveringAcceptFailSet c₁ ε) ≤ tol` は huge-ε (有限最大偏差超) で jointly-typical set=全空間 → fail set ∅ → mass 0 が任意 c₁/tol で成立し**空虚**。A3 decoder は独自 ε' を bind し `C2 ⊆ E2` は**同一半径**を要すので C2 unbounded のまま。→ 半径 **pin** 必須 (Approach step 1)。(ii) **第5軸 = dα'-d scaling**: tolerance は `distortionMax d` 基準だが結論は `distortionMax dα'` で scale、繋ぐ仮説なし (反例 `d≡0 (tol=δ/16), dα'≡5, 0<Pr[C2]≤δ/16 ⇒ distortionMax dα'·Pr[E2]≥5·Pr[C2]>δ/4`)。FIX = dα'-d reconciliation precondition (D3 call-site `dα':=fun x' g↦d x'.1 g` で `rfl` discharge、Leg C.5 同型)。**逸脱評価**: implementer の double-exp 拒否は正当 (M-decay で hM_ub 下不可) だが置換した free-∃ε も vacuous、正しいのは pinned-ε。**教訓 (durable、proof-pivot-advisor)**: WZ 署名-fix を closed と宣言する前に **全 free binder (ε/dα'/M/d') を退化極値で instantiate する check を必須化** (Leg C.5 `d':=0` / 第4軸 all-atypical / 本 #7 の huge-ε・dα'≫d は同一 pattern)。**追加教訓**: 2 sub-lemma が opposite monotone 方向に押す共有 param (ε: acceptance で decreasing / confusion で smallness 要) は片方内で量化不可 — `∃` は片極で vacuous、`∀`-range は他極で偽。**最近共通祖先 (D3) で構造 gap (rate margin) から選ぶ explicit shared input 化**が唯一 honest。**RESOLVED** (pinned-ε rework `cf7d57cd`、独立監査 all-PASS、退化 binder table 全 BLOCKED)。
8. **第6軸 = C2 closure mechanism が Markov Lemma (S5a/gateway-2 でない) + 2 sorry 非対称 (r7 pivot-advisor、2026-07-12、orchestrator 独立 refutation CONFIRMED、active、本線)**: r6 で署名は honest tier-2 になったが、body fill dispatch (r7) で implementer が両 sorry stall。pivot-advisor 判定 = **2 sorry は同一 blocker でなく非対称**。**A3 (`wz_exists_binning_E2_bound:3138`) = tractable NOW**: C2 mass 下界を*仮説* `hcov_accept` (L3153-3158) で取るので、残 work = {decoder≠true covering word}⊆C2∪E2b (`wzBinTypicalDecoder_eq_of_unique:1180` 対偶) + C2 は premise + E2b は S5b(`:1344` `@audit:ok`)+D2(`:1897` `@audit:ok`、per-fixed-codeword ゆえ joint-seq 独立不要)+β'→β Y-marginal transfer + `wzMutualInfoYU_eq_mutualInfo` (Operational.lean:230) bridge、`hε_conf` が confusion 指数<0 保証。assets 全存在、1-2 dispatch。**covering atom C2 conjunct = 真の blocker**: #6 の「S5a+gateway-2 ~40行 Fubini」は **mis-mechanization** (settled-facts 参照)。C2 = 相関-joint acceptance concentration = **Markov Lemma** (Mathlib+codebase 双方に不在、`conditionalStronglyTypicalSlice_mass_ge:1274` は下界・独立 ingredient 止まり)。→ **leg F で self-build (~100-300行、gateway-atom-first で壁/tractable 判定)**、C2 を named sub-lemma `wz_covering_chosenWord_sideInfo_typical` に isolate。**FORWARD (B+D)**: (1) plan mechanism 訂正 (本 commit DONE)、(2) A3 fill dispatch (r7)、(3) C2 を named Markov sub-lemma に isolate。**教訓 (durable、#6 family 第3実例)**: residual の named closure mechanism が **別 measure (product/独立 vs 相関 joint) or 別 functional (cover-x vs test-y) の lemma** を再利用しているときは、event 名の一致 (「acceptance」) を mechanism の一致と取り違えるな。effort 見積り前に **conclusion の集合所属述語の measure AND functional が residual と一致するか**を verbatim 確認。stale path 訂正: `distortion_le_distortionMax` は `RateDistortion/AchievabilityAsymptoticFailureDecay.lean` (旧 plan の `FailureDecay.lean:116` は不在)。
