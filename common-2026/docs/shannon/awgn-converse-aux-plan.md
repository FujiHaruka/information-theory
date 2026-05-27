# AWGN Converse aux — F-3 analytic discharge ムーンショット計画 🌙 (T2-A Tier-3 follow-up)

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) §「撤退ライン F-3」。
> **Sibling plans**: F-1 [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md) / F-2 [`awgn-mi-bridge-plan.md`](awgn-mi-bridge-plan.md) / F-2 deeper [`awgn-mi-decomp-plan.md`](awgn-mi-decomp-plan.md) / peer migration [`awgn-f1-f3-peer-simultaneous-migration-plan.md`](awgn-f1-f3-peer-simultaneous-migration-plan.md) / F-4 [`awgn-f1-discharge-moonshot-plan.md`](awgn-f1-discharge-moonshot-plan.md) (DONE 148 行)。
>
> **Status (2026-05-27)**: peer migration により `IsAwgnConverseHypothesis` 削除済、Phase C 完了 + 後続 mini-plan [`awgn-main-converse-wiring-mini-plan.md`](awgn-main-converse-wiring-mini-plan.md) closure により `Common2026/Shannon/AWGNConverse.lean` の `awgn_converse` body は `awgn_converse_F3_discharged` への 1 行 `exact` で discharge 済、file scope 0 sorry / 0 @residual = **proof done at file scope**。残置 wall residual は `AWGNConverseDischarge.lean:405` `awgnConverseJoint_pair_mi_ne_top` (`@residual(wall:multivariate-mi)`) に集約維持 — project scope の proof done は wall:multivariate-mi closure (M5 未起草) 待ち。判断ログ #6 後続送り (4) closure 完了。
>
> **Phase 0 inventory ✅** (`awgn-converse-aux-mathlib-inventory.md` ~360 行、5 判断 verbatim 確定 — 判断ログ #1)。**最大発見**: `shannon_converse_single_shot` (`Common2026/Shannon/Converse.lean:81`) が Fano + DPI postprocess + entropy chain + `H(W uniform) = log M` を 1 補題に packaging 済 (Y 側 `[MeasurableSpace Y]` のみ)。Phase B-Fano は 1 行呼出に圧縮。
>
> **規模**: 中央 ~520 行 / 悲観 ~810 行 (T-FFC-4 1000 行未満確実)。
>
> **Goal**: `Common2026/Shannon/AWGNConverseDischarge.lean` 新規 publish (姉妹 `AWGNAchievabilityDischarge.lean` と対称)、`isAwgnConverseFeasible_discharger (P N h_meas h_feasible M n c Pe hPe) : log M ≤ n·(1/2)log(1+P/N) + binEntropy(Pe) + Pe·log(M-1)` + `awgn_converse_F3_discharged` wrapper。最終的に `AWGNConverse.lean:70` の `sorry` を呼出に置換、staged hyp 1 本 (bundle predicate) は後続 plan (`awgn-converse-feasible-discharge-plan.md` 未起草) に委ねる 2 段構成。
>
> **撤退ライン (本 plan 内)**: T-FFC-1 (Fano StandardBorelSpace 型クラス) / T-FFC-2 (per-letter integrability `h_ent_int` Mathlib 壁、最有力) / T-FFC-3 (continuous MI chain rule Mathlib 壁) / T-FFC-4 (規模超過、低確率) / T-FFC-5 (Pe bridge 肥大、新規)。詳細 §撤退ライン。
>
> **honesty 規律**: bundle は regularity (Mathlib 壁 packaging)、load-bearing ではない。4 条件: (a) 結論型 ≠ `awgn_converse` 結論 / (b) Mathlib 壁明示 / (c) Phase B で genuine assembly / (d) `@audit:staged(awgn-converse-feasible)`。

## 進捗

- [x] Phase 0 — Mathlib + Common2026 在庫 (Fano measure form / DPI continuous / continuous MI chain rule / Gaussian Y max-entropy / per-letter integrability) ✅ → [`awgn-converse-aux-mathlib-inventory.md`](awgn-converse-aux-mathlib-inventory.md) (~360 行、5 判断 verbatim 確定、`shannon_converse_single_shot` 圧縮発見)
- [ ] Phase A — bundle predicate `IsAwgnConverseFeasible` 設計 + skeleton 📋
- [ ] Phase B-Fano — Fano application via `fano_inequality_measure_theoretic` (`X := Fin M`, `Y := Fin n → ℝ`) 📋
- [ ] Phase B-DPI/chain — DPI `I(W;Ŵ) ≤ I(X^n;Y^n)` + memoryless chain `I(X^n;Y^n) ≤ ∑ I(X_i;Y_i)` 📋
- [ ] Phase B-Gaussian — per-letter `I(X_i;Y_i) ≤ (1/2) log(1+P/N)` (Gaussian Y_i max-entropy) 📋
- [ ] Phase C — `isAwgnConverseFeasible_discharger` 統合 + `awgn_converse_F3_discharged` wrapper 📋
- [ ] Phase V — verify (lake env lean silent / 0 sorry / 1 staged bundle / `AWGNConverse.lean` の `sorry` を呼出に置換 / `Common2026.lean` 編入) 📋

## ゴール / Approach

### Goal (最終 signature の SoT はコード)

最終 publish 形は `Common2026/Shannon/AWGNConverseDischarge.lean` の `isAwgnConverseFeasible_discharger` + `awgn_converse_F3_discharged` wrapper。bundle `IsAwgnConverseFeasible` は **3 sub-bound 連言** (Phase 0 判断 #1 確定): `PerLetterIntegrabilityForConverse ∧ ContinuousMIChainRuleForConverse ∧ MarkovChainForConverse`。前 2 staged (Mathlib 壁、T-FFC-2/3)、後 1 genuine (regularity、`mutualInfo_le_of_markov` 経由)。witness 不要 (converse 側 input law が code 由来)。

### Approach (overall strategy)

Cover-Thomas 9.1.2 標準 4 段 (Fano → DPI → memoryless chain rule → per-letter Gaussian max-entropy)。Phase 0 最大発見: `shannon_converse_single_shot` (`Common2026/Shannon/Converse.lean:81`) が (a)+(b)+(e) (Fano + DPI postprocess + entropy chain + `H(W uniform) = log M`) を 1 補題 packaging 済 (Y 側 `[MeasurableSpace Y]` のみ、T-FFC-1 完全回避)。Phase B-Fano は 1 行呼出に圧縮、Mathlib 壁は per-letter integrability + continuous MI chain rule の 2 件に絞れる。

```
(a)+(b)+(e)  shannon_converse_single_shot 呼出     [B-Fano]
             log M ≤ I(W;Y^n).toReal + binEntropy(Pe) + Pe·log(M-1)
             + Pe bridge 自作 (~25-50 行 = T-FFC-5)
(c-DPI)      mutualInfo_le_of_markov (genuine)     [B-DPI]
             I(W;Y^n) ≤ I(X^n;Y^n)  (MarkovChainForConverse 経由)
(c-chain)    bundle staged hyp destructure (T-FFC-3)  [B-chain]
             I(X^n;Y^n) ≤ ∑ I(X_i;Y_i)
(d)          differentialEntropy_le_gaussian_of_variance_le      [B-Gaussian]
             I(X_i;Y_i) ≤ (1/2) log(1+P/N)  (`h_ent_int` staged = T-FFC-2)
(f)          chain assembly                          [Phase C]
```

**Mathlib-shape-driven definitions** (詳細はコード docstring + Phase 0 inventory SoT):
- Single-shot converse 圧縮 → 判断 #2 (inventory §B、Phase B-Fano 1 行呼出 + `hMI_finite` ~10-20 行 + Pe bridge ~25-50 行 = T-FFC-5)。
- per-letter Gaussian max-entropy → `differentialEntropy_le_gaussian_of_variance_le` 4-hyp 形、`h_ent_int` のみ Mathlib 壁 (判断 #5)。3-of-4 (`hμ ≪ vol` / mean / var / var_int) は本 plan 内 genuine 化可。
- continuous MI chain rule → `Fintype α` 制約付き既存補題は AWGN reuse 不可、`mutualInfo_pi_eq_sum` も iid joint 仮定で発火不可 → bundle staged hyp (T-FFC-3、判断 #4)。姉妹 `awgn-mi-decomp-plan.md` Phase 6 と相補。
- DPI continuous → `mutualInfo_le_of_markov` (`CondMutualInfo.lean:385`、Y `[StandardBorelSpace]` 自動充足) で genuine 化 (判断 #3)。`MarkovChainForConverse` field は regularity hyp、staged 不要。

### 規模見積もり

中央 **~520 行** (起草時 ~650 → inventory 反映 -130 行)、悲観 ~810 行。内訳: Phase A ~100 / B-Fano ~60 / B-DPI ~70 / B-chain ~40 / B-Gaussian ~150 / Phase C ~50 / skeleton ~50。T-FFC-4 (1000 行) 発動しない見込み。姉妹 achievability discharge (1641 行) より大幅小 (converse は randomization 不在 + `shannon_converse_single_shot` 圧縮)。

### ファイル構成

新規: `Common2026/Shannon/AWGNConverseDischarge.lean` (Phase A-C 集約)、`docs/shannon/proof-log-awgn-converse-aux-phase[A-C].md` (yes 指定 Phase のみ)。既存依存: `AWGNConverse.lean` (line 70 sorry 置換対象) / `AWGN.lean` / `AWGNMain.lean` / `AWGNF1Discharge.lean` / `DifferentialEntropy.lean` / `ChannelCoding.lean` / `MutualInfo.lean` / `CondMutualInfo.lean` / `MIChainRule.lean` / `Fano/Measure.lean` / `AWGNAchievabilityDischarge.lean` (姉妹 1641 行)。Phase V で `Common2026.lean` 1 行追加 (orchestrator)。

**imports** (`import Mathlib` 禁止): 上記 Common2026 modules + `Mathlib.Probability.{Distributions.Gaussian.Real,Independence.Basic}` + `Mathlib.MeasureTheory.{Constructions.Pi,Function.LpSpace.Basic}`。追加は loogle で確定。

## 依存関係 (Mathlib + Common2026 既存)

利用可 (verbatim 確認済、SoT はコード):
- `fano_inequality_measure_theoretic` (`Fano/Measure.lean:226`)
- `differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:518`、4-hyp 形、`h_ent_int` のみ staged 対象)
- `differentialEntropy_gaussianReal` (`DifferentialEntropy.lean:412`)
- `mutualInfoOfChannel` / `_eq_mutualInfo_prod` (`ChannelCoding.lean:85/96`)
- AWGN defs (`AWGN.lean:64-100`)、姉妹 bundle pattern (`AWGNAchievabilityDischarge.lean`)
- `mutualInfo_le_of_markov` (`CondMutualInfo.lean:385`)、`mutualInfo_le_of_postprocess` (`DPI.lean:142`、無 Fintype)
- `shannon_converse_single_shot` (`Converse.lean:81`、Y `[MeasurableSpace]` のみ、判断 #2)

Phase 0 で裏取り済 (5 軸、`awgn-converse-aux-mathlib-inventory.md` SoT): DPI continuous / continuous MI chain rule / per-letter input power / per-letter `h_ent_int` 壁判定 / entropy chain + `H(W)=log M` 在庫。

参考 (import しない、`Fintype α` 想定で AWGN reuse 不可): `ChannelCodingConverse{General,GeneralStrong,MemorylessPure}.lean`。

---

## Phase 0 — Mathlib + Common2026 API 在庫 ✅ (2026-05-27 完了)

`awgn-converse-aux-mathlib-inventory.md` (~360 行) 5 判断 verbatim 確定。bundle 3 field (PerLetter staged ∧ Chain staged ∧ Markov genuine) / `shannon_converse_single_shot` 圧縮発見 / DPI genuine 化可 / chain rule staged 確定 / `h_ent_int` のみ wall。新規 T-FFC-5 (Pe bridge) 提案。詳細 → 判断ログ #1。

---

## Phase A — bundle predicate `IsAwgnConverseFeasible` 設計 + skeleton ✅ (判断ログ #2)

`AWGNConverseDischarge.lean` 318 行 publish。bundle = 3 field 連言 + `[NeZero M]` typeclass binder 追加 (`IsMarkovChain` の `[IsFiniteMeasure μ]` 要件)。Local def 4/5 genuine 化 (`awgnConverseJoint` / `perLetterYLaw` / `perLetterMI` / `jointMIWYn` / `jointMIXnYn`)、1 件 def-level sorry (`instIsProbabilityMeasure` total mass、Phase B-DPI で fill)。独立 honesty audit PASS-WITH-REMARKS (15 件、defect 0、tier 5 なし)。詳細 → 判断ログ #2。

---

## Phase B-Fano — `shannon_converse_single_shot` 1 行呼出 + Pe bridge 📋

**スコープ**: Cover-Thomas 9.1.2 (a)+(b)+(e) を `shannon_converse_single_shot` 1 行呼出で吸収 (`X := Fin M, Y := Fin n → ℝ, decoder := c.decoder`、T-FFC-1 完全回避)。出力 `awgn_converse_single_shot_call` の signature: `log M ≤ (jointMIWYn c h_meas).toReal + binEntropy(Pe) + Pe · log(M-1)`。

**Sub-steps** (~30-100 行、0.5-1 session):
- B-Fano-1 Ω 構築 (`Fin M × (Fin n → ℝ)`、uniform W ⊗ product channel、measurability + uniform 表現 plumbing ~15-25 行)
- B-Fano-2 `hMI_finite : mutualInfo μ Msg Yo ≠ ∞` 確保 (~10-20 行)
- B-Fano-3 (**T-FFC-5**) AWGN `Pe = (1/M) ∑ errorProbAt m` と Fano `errorProb` の bridge (uniform W + product channel Fubini、~25-50 行)
- B-Fano-4 `shannon_converse_single_shot` 1 行呼出

**依存** (verbatim 確認済): `shannon_converse_single_shot` (`Converse.lean:81`) / `Measure.pi` / `Measure.count` / AWGN `errorProbAt` (`ChannelCoding.lean:195`) / Fano `errorProb` (`Fano/Measure.lean:74`)。`fano_inequality_measure_theoretic` / `H(W)=log M` / entropy chain rule の直接呼出不要 (判断 #2)。

**Done**: `awgn_converse_single_shot_call` publish 0 sorry / `lake env lean` clean / proof-log `phaseB-fano`。

**Fallback**: T-FFC-5 (Pe bridge 50+ 行) → 独立補題化 / `hMI_finite` 困難 → local 補題 / `Fintype.card_fin` cast plumbing → `simpa` 吸収。

---

## Phase B-DPI/chain — Markov DPI (genuine) + memoryless chain rule (staged) 📋

**スコープ**: Cover-Thomas 9.1.2 step 2-3: `I(W;Y^n) ≤ I(X^n;Y^n) ≤ ∑ I(X_i;Y_i)`。DPI 側 genuine (`mutualInfo_le_of_markov` + `MarkovChainForConverse` destructure、判断 #3)、chain 側 staged hyp destructure (T-FFC-3 確定、判断 #4)。

**Sub-steps** (~60-180 行、1-1.5 session):
- B-DPI-1 `awgn_dpi` (~40-70 行): `mutualInfo_le_of_markov` 1 行呼出 + Markov chain plumbing。`[StandardBorelSpace]` 自動充足 (`instStandardBorelSpacePi`)。
- B-chain-1 `awgn_chain_rule` (~20-40 行): bundle staged hyp destructure → direct apply。

**依存**: `mutualInfo_le_of_markov` (`CondMutualInfo.lean:385`) / `IsMarkovChain` (`CondMutualInfo.lean:73`) / `instStandardBorelSpacePi` / staged `ContinuousMIChainRuleForConverse` / 姉妹 `awgn-mi-decomp-plan.md` Phase 6 と相補。

**Done**: `awgn_dpi` / `awgn_chain_rule` 0 sorry / `lake env lean` clean / proof-log `phaseB-dpi-chain`。

**Fallback**: Markov chain genuine 構築 hard → local 補題 (~30 行) / chain rule 壁深 → 現方針 staged で進行 / typed RV vs klDiv mismatch → 姉妹 `awgn-mi-bridge` dependency。

---

## Phase B-Gaussian — per-letter `I(X_i; Y_i) ≤ (1/2) log(1+P/N)` 📋

**注意**: Phase C 再設計後 (判断ログ #6)、起草時の `awgn_per_letter_mi_le_capacity` (per-letter 形) は **false-statement defect により撤回済**。本 Phase の出力は C-1b `awgn_per_letter_mi_le_log_var` (per-letter variance 引数化形) に統合される。

**Sub-steps** (Cover-Thomas 9.1.2 step 4、~120-250 行、1.5-2 session):
- B-Gauss-1 avg power: `(1/n) ∑ E[X_i²] = (1/M)(1/n) ∑_m ∑_i (encoder m i)² ≤ P` (Fubini swap)
- B-Gauss-2 `Y_i` law: `μ_{Y_i} = μ_{X_i} ∗ N(0,N)` (convolution)
- B-Gauss-3 `Var(Y_i) ≤ P + N` (independence)
- B-Gauss-4 Gaussian max-entropy `differentialEntropy_le_gaussian_of_variance_le` 起動 (4 hyp、`h_ent_int` のみ bundle staged hyp 経由)
- B-Gauss-5 `h(Y_i|X_i) = h(Z_i) = (1/2)log(2πeN)` (shift-invariance + `differentialEntropy_gaussianReal`)
- B-Gauss-6 `I = h(Y_i) - h(Y_i|X_i)` (F-2 bridge per-letter 形、姉妹 `awgn-mi-bridge` / `awgn-mi-decomp` Phase 7 完了で genuine 化)
- B-Gauss-7 結合: `(1/2)log((P+N)/N) = (1/2)log(1+P/N)`

**依存**: `differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:518`) / `differentialEntropy_gaussianReal` (`:412`) / Mathlib `gaussianReal_conv_gaussianReal` / `gaussianReal_add_gaussianReal_of_indepFun` / `variance_id_gaussianReal` / `integral_id_gaussianReal` / staged `PerLetterIntegrabilityForConverse` / F-2 bridge (姉妹 plan)。

**Done**: B-Gauss-1~7 0 sorry / `lake env lean` clean / proof-log `phaseB-gaussian`。

**Fallback**: B-Gauss-2 Y_i convolution shape mismatch → Y_i 法を bundle hyp packing (T-FFC-2 拡張) / F-2 bridge shape mismatch → per-letter bridge を hyp 引数外出し。

---

## Phase C — `isAwgnConverseFeasible_discharger` 統合 + wrapper 📋 (Phase B audit verdict 反映で再設計、判断ログ #6 で実装済)

Phase B-Gaussian の per-letter `E[X_i²] ≤ P` 形が AWGN per-message block constraint から genuine 化不能 (tier 5 false-statement defect)、`awgn_per_letter_mi_le_capacity` 撤回 + **sum-form + Jensen** 構造で直接 publish に再設計。

**Sub-steps** (~210-410 行、1-2 session、判断ログ #6 で実装済 823 行):
- C-1a `awgn_per_letter_input_power_avg`: `(1/n) ∑_i E[X_i²] ≤ P` (Fubini swap、~10-20 行、genuine)
- C-1b `awgn_per_letter_mi_le_log_var`: per-letter variance 引数化形 Gaussian max-entropy (4 hyp 充足、~80-150 行、`h_ent_int` のみ staged)
- C-1c `sum_log_one_add_le_n_log_one_add_avg`: Jensen / `Real.log` concavity (~30-60 行)
- C-2 `awgn_sum_per_letter_mi_le_n_capacity`: C-1a+1b+1c 合成 (~20-40 行)
- C-3 `isAwgnConverseFeasible_discharger` body: B-Fano → DPI → chain → C-2 の chain assembly (~30-60 行、bundle 3 sub-bound destructure)
- C-4 `awgn_per_letter_mi_le_capacity` 撤回 (C-1b が代替)
- C-5 transitive MI 有限性 helper `awgnConverseJoint_mutualInfo_ne_top_via_chain` (~20-40 行、`awgn_dpi` inline + Fano helper 両方 0 sorry へ)
- C-6 `awgn_converse_F3_discharged` wrapper (`haveI : NeZero M := ⟨by omega⟩` 含む、~10-20 行)
- C-7 `AWGNConverse.lean:70` body 置換 (orchestrator 実施、判断 #6-B で independent wrapper route 確定)

**Done**: C-1a〜C-7 publish / `AWGNConverseDischarge.lean` clean (sorry 残: bundle 2 staged + C-1b/C-1c/C-5 残置 5 件、判断ログ #6) / `AWGNConverse.lean` clean / `Common2026.lean` 1 行追加 (Phase V) / 独立 honesty audit subagent 起動。proof-log: `phaseC`。

**Fallback**: C-1c Jensen 発火しない → `log((N+x)/N) = log(N+x) - log(N)` 分離 + `Real.strictConcaveOn_log_Ioi` 直接 / C-1b 4 hyp hard → bundle 4 field pivot (3 → 4) / C-3 destructure complex → `structure` 化 + dot accessor / C-5 hard → 別 plan `awgn-mi-finite-cont-plan.md` 委譲 / `AWGNConverse.lean:70` signature mismatch → 本 file 内で直接書換 (判断 #6-B で採用、wrapper route)。

---

## Phase V — verify + Common2026.lean 編入準備 📋

**Done** (0.25 session、proof-log: no): `AWGNConverseDischarge.lean` / `AWGNConverse.lean` 両 silent / `@residual(plan:...)` → `@audit:staged(awgn-converse-feasible)` 降格 / 独立 honesty audit subagent 起動 (bundle 4 条件 verify) / `Common2026.lean` に `import Common2026.Shannon.AWGNConverseDischarge` 追加。

---

## 撤退ライン

**Scope 縮小ライン**:
- **T-FFC-1** Fano `[StandardBorelSpace (Fin n → ℝ)]` 自動推論失敗 → local instance derive (~10-20 行)
- **T-FFC-2** per-letter integrability `h_ent_int` Mathlib 壁 (最有力) → bundle `PerLetterIntegrabilityForConverse` staged packing、closure は `awgn-converse-feasible-discharge-plan.md` (未起草)。honesty 4 条件: 結論型 ≠ / "Mathlib gap" docstring / Phase B 本物 assembly / `@audit:staged(awgn-converse-feasible)` タグ
- **T-FFC-3** continuous MI chain rule Mathlib 壁 (確定発動) → bundle `ContinuousMIChainRuleForConverse` staged、姉妹 `awgn-mi-decomp-plan.md` Phase 6 と相補
- **T-FFC-4** 規模超過 ~1000 行超 (低確率、悲観 ~810 行で発動しない見込み) → 2 file 分割 (`...Fano.lean` + `...Perletter.lean`)
- **T-FFC-5** `shannon_converse_single_shot` Pe bridge 50+ 行肥大 (新規、Phase 0 由来) → 独立補題 `awgn_errorProb_eq_fano_errorProb` 切出、本体 1 行呼出

**honesty 撤退ライン** (常時): name laundering 禁止 / `IsAwgnConverseFeasible` 中身が conclusion-as-hypothesis 化禁止 / Phase C body が `h_feasible …` 1 行縮退禁止。CLAUDE.md「検証の誠実性」tells で機械的に検出。姉妹 `awgn-achievability-typicality-plan.md` 同型。

**load-bearing 禁止規律** (判定軸): bundle 3 sub-bound (`PerLetter` / `Chain` / `Markov`) はすべて **regularity** 側 (結論型 ≠ `awgn_converse` 結論、Mathlib 壁 packaging or structural fact)。禁止例 `IsAwgnConverseClaim := ∀ ..., log M ≤ n·C + binEntropy + …` は load-bearing tier 5。詳細 → §「honesty 規律」 + CLAUDE.md「load-bearing hypothesis bundling」。

---

## Risk table

| Risk | 確率 | 影響 | 緩和 |
|---|---|---|---|
| per-letter integrability Mathlib 壁 | 高 | 中 | T-FFC-2 staged、後続 plan |
| continuous MI chain rule Mathlib 壁 | 高 | 中 | T-FFC-3 staged、姉妹 `awgn-mi-decomp` |
| DPI continuous Mathlib 壁 | 低 (判断 #3 genuine 化可) | 低 | `mutualInfo_le_of_markov` |
| Fano StandardBorelSpace 推論失敗 | 中 | 低 | T-FFC-1 local instance |
| F-2 bridge shape mismatch | 中 | 中 | per-letter bridge hyp 外出し |
| Pe bridge 肥大 | 中 | 中 | T-FFC-5 独立補題化 |
| input power plumbing 肥大 | 低-中 | 低 | uniform W avg、必要なら local 補題 |
| 規模超過 1000+ | 低 | 中 | T-FFC-4 (発動しない見込み) |
| honesty defect 混入 | 低 | 高 | §honesty 規律 + Phase V audit |
| `awgn-mi-decomp` Phase 6 scope 重複 | 低 | 中 | 姉妹 closure で staged→genuine 書換可 |

---

## 親 plan / 兄弟 plan との scope 区別

| Plan | スコープ | 状態 |
|---|---|---|
| `awgn-moonshot-plan.md` (親) | T2-A 全体 | DONE |
| `awgn-achievability-typicality-plan.md` (F-1) | achievability core | DONE (1641 行、3 staged) |
| `awgn-mi-bridge-plan.md` (F-2) | MI ↔ h(Y) - h(Y|X) bridge | 起草中 |
| `awgn-mi-decomp-plan.md` (F-2 deeper) | continuous MI chain rule body | 起草中 |
| **本 plan** (F-3) | Fano + DPI + chain + per-letter Gaussian | **起草中** |
| `awgn-f1-f3-peer-simultaneous-migration-plan.md` | peer migration | DONE (本 plan 起点 Tier 2 作成) |
| `awgn-f1-discharge-moonshot-plan.md` (F-4) | kernel measurability | DONE (148 行) |

本 plan は peer-migration の出口 successor。`ContinuousMIChainRuleForConverse` は `awgn-mi-decomp` Phase 6、F-2 per-letter bridge は `awgn-mi-bridge` / `awgn-mi-decomp` Phase 7 closure で自動 discharge 候補。

---

## オーケストレータ注記

- 実装 agent は `Common2026.lean` 編集しない (Phase V で orchestrator)
- Phase 単位 proof-log: A/B yes、C/V no
- Phase A 完了後 + Phase C 完了後 + Phase V で独立 honesty audit subagent 必須 (新規 sorry/staged predicate/signature 改変のため、CLAUDE.md)
- Phase B-Fano (山場 #1): `fano_inequality_measure_theoretic` の type-class 整合再 verbatim 確認
- Phase B-chain (山場 #2): staged 確定見込み、`awgn-mi-decomp` Phase 6 で genuine 書換可

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### #0 (2026-05-27) plan 起草 — peer migration 出口 successor

peer migration commit で Tier 2 sorry 状態。姉妹 `awgn-achievability-typicality-plan.md` (1641 行、3 staged bundle `IsAwgnRandomCodingFeasible`) と対称構造を採用 — converse は randomization 不在で中央 ~650 行予測 (起草時、後に inventory で ~520 行下方修正)。

### #1 (2026-05-27、Phase 0 inventory) bundle structure + 5 判断 確定

5 軸 inventory (`awgn-converse-aux-mathlib-inventory.md` ~360 行、SoT) 完了:
- 判断 #1: 3 field = PerLetter staged ∧ Chain staged ∧ Markov genuine、witness 不要
- 判断 #2: `shannon_converse_single_shot` (`Converse.lean:81`) で Fano+DPI postprocess+entropy chain+`H(W)=log M` 1 補題 packaging 済、Y 側無制約 → Phase B-Fano 1 行圧縮
- 判断 #3: DPI continuous genuine 化可 (`mutualInfo_le_of_markov` `CondMutualInfo.lean:385` + `[StandardBorelSpace]` 自動充足)、Markov field は regularity
- 判断 #4: continuous MI chain rule 壁深度 large staged 確定 (T-FFC-3、`Fintype α` 既存補題 + `mutualInfo_pi_eq_sum` iid joint 両方 reuse 不可)、姉妹 `awgn-mi-decomp` Phase 6 相補
- 判断 #5: per-letter `h_ent_int` 壁深度 medium staged 確定 (T-FFC-2)、4 hyp の他 3 は genuine 化可、forall packing

規模再見積 ~650 → ~520 (-130)、悲観 ~810。新規 T-FFC-5 (Pe bridge 50+ 行肥大) 追加。

### #2 (2026-05-27、Phase A 完了) bundle predicate 確定形

`AWGNConverseDischarge.lean` 318 行 skeleton publish。bundle に `[NeZero M]` typeclass binder 追加 (`IsMarkovChain` の `[IsFiniteMeasure μ]` 要求、`2 ≤ M ⇒ NeZero M` は consumer `haveI` で 1 行)。Local def 4/5 closed form 化、1 件のみ def-level sorry (`instIsProbabilityMeasure` total mass、Phase B-DPI で fill)。

独立 honesty audit subagent: **PASS-WITH-REMARKS** — 6 条件 (a)-(f) 全 OK、15 declaration table defect 0、tier 5 なし。REMARKS: AWGN family sweep で `@audit:staged(awgn-{random-coding,converse}-feasible)` 同時 migrate / 姉妹 `awgn-mi-decomp` Phase 6 closure で `ContinuousMIChainRuleForConverse` staged → genuine 書換候補。

### #3 (TBD、Phase B-Fano 完了時) Fano application + type-class 整合

`fano_inequality_measure_theoretic` を AWGN substitution で起動、T-FFC-1 発動状況を記録。

### #4 (TBD、Phase B-DPI/chain 完了時) DPI + chain rule 壁発動

staged `DPIForConverse` / `ContinuousMIChainRuleForConverse` の着地形 (staged vs genuine) を記録。

### #5 (TBD、Phase B-Gaussian 完了時) F-2 bridge per-letter 処理

姉妹 `awgn-mi-bridge` / `awgn-mi-decomp` との shape 整合 / hyp 外出し状況を記録。

### #6 (2026-05-27、Phase C dispatch 完了) `AWGNConverse.lean:70` 置換ルート

**採用 #6-B** (`AWGNConverseDischarge.lean` 内 independent wrapper、`AWGNConverse.lean` 無変更)。理由: wrapper signature が `h_feasible` + `h_mi_bridge_per_letter` + `hn_pos` 追加要求、`awgn_converse` 既存 signature と不整合 → 直接置換は `AWGNMain.lean` migration まで影響拡大。Phase V で orchestrator が `AWGNMain.lean` とセット実施 (別 mini-plan `awgn-main-converse-wiring-plan.md` 候補)。

Phase C 完成度: `AWGNConverseDischarge.lean` 823 行 (A 318 + B 305 + C +200)、5 sorry 残置 全 `@residual(plan:awgn-converse-aux-plan)`:
- L389 `awgnConverseJoint_mutualInfo_ne_top` (Fano-side、wall:MI-finiteness)
- L468 `awgn_dpi` inline (X^n MI 有限性、wall:MI-finiteness)
- L603 `awgn_per_letter_mi_le_log_var` (C-1b、wall:gaussian-max-entropy-4hyp)
- L624 `sum_log_one_add_le_n_log_one_add_avg` (C-1c、wall:jensen-affine-subst)
- L732 `awgnConverseJoint_mutualInfo_ne_top_via_chain` (C-5、wall:MI-finiteness-bridge)

`awgn_per_letter_mi_le_capacity` 撤回完了 (`@audit:defect(false-statement)` タグ除去)。bundle 3 field 維持。`AWGNConverse.lean:70` body sorry 維持 (C-7 fallback)。

Genuine assembly: C-1a (Fubini swap) / C-2 (mechanical chain) / C-3 (B-Fano+DPI+chain+C-2 chain assembly) / C-6 (`haveI : NeZero M`+ discharger 呼出)。

後続セッション送り: (1) C-1b 4 hyp 充足 単独 mini-plan / (2) C-1c Jensen affine subst — `Real.log(1+x/N)` concavity 補題 + Jensen helper 分離 / (3) C-5 transitive MI 有限性 — C-1b 完成後 ENNReal 形 per-letter 経由 (`.toReal ≤ R` 退化境界回避) / (4) `AWGNConverse.lean:70` 置換 — `AWGNMain.lean` とセット **→ closure 済 (判断 #7、`awgn-main-converse-wiring-mini-plan.md`)**。

### #7 (2026-05-27、後続セッション送り (4) closure) `awgn-main-converse-wiring-mini-plan` 完了

mini-plan [`awgn-main-converse-wiring-mini-plan.md`](awgn-main-converse-wiring-mini-plan.md) closure (M1-M4 全完了)。`Common2026/Shannon/AWGNConverse.lean` の `awgn_converse` body は `awgn_converse_F3_discharged P hP N hN h_meas h_feasible h_mi_bridge_per_letter hM hn_pos c Pe hPe` への 1 行 `exact` で discharge、新引数 3 件 (`h_feasible` / `h_mi_bridge_per_letter` / `hn_pos`) pass-through 済。

採用方針 (i): `AWGNConverse.lean:2` で `import Common2026.Shannon.AWGNConverseDischarge` 新規追加、逆向き import (`AWGNConverseDischarge → AWGNConverse`) は不発火 (verbatim grep 確認済) → 循環依存なし。

verify (orchestrator `lake env lean` 実行済):
- `AWGNConverse.lean`: 0 errors / 0 sorry / 0 @residual = **proof done at file scope**
- `AWGNConverseDischarge.lean`: 0 errors / 1 sorry (line 405 `awgnConverseJoint_pair_mi_ne_top`、`@residual(wall:multivariate-mi)`、M3 状態維持)
- `AWGNMain.lean`: 0 errors / 0 sorry / 0 @residual

採用 tag (`AWGNConverse.lean:71`): `@audit:closed-by-successor(awgn-converse-aux-plan, wall-multivariate-mi)` (`audit-tags.md`「closed-by-successor」語彙準拠、body が wall に伝播するため `@audit:partial-ok` ではなく `closed-by-successor` を選定)。consumer ripple = 0 件 (mini-plan 起草時判定通り)。

**本 plan の残課題**: 後続セッション送り (1)-(3) (C-1b / C-1c / C-5) のみ。`AWGNConverse.lean` の `awgn_converse` body sorry は閉じたが、`AWGNConverseDischarge.lean` 内の 5 sorry (判断 #6 列挙) は維持 → project scope の proof done は wall closure 完了待ち。

### #8 (TBD、Phase V 完了時) 規模実績 + honesty audit verdict

実績 LOC / 0 sorry 状況 / staged hyp 数 / 独立 audit verdict / `@audit:staged(awgn-converse-feasible)` タグ整合。本 plan 完了で `awgn_converse` body sorry 解消、staged hyp 1 本残置 → `awgn-converse-feasible-discharge-plan.md` (未起草) に委譲。
