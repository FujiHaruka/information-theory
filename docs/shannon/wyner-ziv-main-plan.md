# Wyner–Ziv operational main theorem (achievability + converse) サブ計画

> **Parent**: [`wyner-ziv-moonshot-plan.md`](wyner-ziv-moonshot-plan.md) §operational main relay

**Status**: ACTIVE 🚧 — **converse (P2) は FULLY CLOSED sorry-free + 独立監査 PASS (leg 11)**。最後の converse own-sorry `wz_support_reduce` を route C (K=`|α|+3`、bare ambient Carathéodory) で genuine closure → **`wyner_ziv_converse` は sorryAx-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`、`@audit:ok`)**。converse own-sorry は **ゼロ**。**achievability P3 (leg 15): S1/S2/C/E の 4 sub-lemma + top-level reduction を sorry-free closure (`@audit:ok`、独立監査 ALL-OK)。top-level `wz_goodCode_exists_of_testChannel` は E∘BD reduction (`wz_diagonalize_slack (wz_perDelta_codes_exist …)`、signature 不変 = full-support 仮説不追加 crux 維持)。**leg 16: BD の steps 1-2 seam を sorry-free closure** (`wz_coveringDistortion_reconcile` + `wz_coveringFamily_of_testChannel`、両 `@audit:ok`、独立監査 ALL-OK `4b7f6441`)。**leg 17: BD steps 3-7 を S3-S7 sub-lemma へ skeleton 分解** (`400f9308`/`f6f31b83`、独立監査 2 pass): S3 `wzCodeOfCoveringBinning` / S4 `wzBinTypicalDecoder`(+uniqueness) / S7 `wzLiftSupportCode` の def を sorry-free closure + BD body を capstone S6 への own-sorry ゼロ reduction 化。S5a body も sorry-free closure (`35941c54`、`@audit:ok`)。**leg 18: S5b crux `wz_codebook_confusion_expectation_le` を sorry-free closure** (`356c8f25`、`@audit:ok` 独立監査 PASS `eebd88f5`): outer-sum-first (biUnion over `m':Fin M₁` → per-`m'` Tonelli swap → `hcollision`+`hmass`)、regularity 前提 `hYs`/`htrueIdx` を Tonelli 用に追加 (load-bearing でない、S6 が discharge)、codebook-restricted union は body 残置 = bundling 回避。**leg 19: S6→(D)+(B) 分解** — D1 rate-identity CLOSED / D2 `wz_covering_codeword_sideInfo_mass_le` CLOSED sorry-free / (B) collision `wzIndexBinningMeasure_collision` CLOSED sorry-free、S6 body は (D) `wz_perDelta_covering_binning_eventual` への sorry-free glue 化。**leg 20+: D3 `wz_perN_covering_binning_code` の under-hyp を子 plan [`wz-binning-covering-plan.md`](wz-binning-covering-plan.md) で段階的に honest 化 — 子 Leg 0 (budget δ-split) / C.5 (reconciliation `hd'_eq`/`hqf`) / C.6 (M-axis `M ≤ exp(nR₁)+1` pin) の 3 軸解消済 + Leg D の G2/A1 (E2-only decomp + lift identity) `@audit:ok` + A2 `wz_ideal_expectation_eq_covering` sorry-free (`84393413`)。D3 body は sorry-free reduction (M-axis defect 除去 honest tier-2 復帰)**。**だが Leg D で第4 under-hyp 軸 = covering-acceptance C2 を発見・独立監査 CONFIRMED**: E2 = E2b(confusion)∪C2(acceptance) で A3 `wz_exists_binning_E2_bound` (Achievability.lean:3022) が C2 を bound する仮説を欠き false-as-framed (`@audit:defect(false-statement)`、反例 all-atypical-image codebook)。**残 literal sorry 1 = A3 のみ**。**次 leg 本線 = 子 Leg E (covering-acceptance C2 再設計 Proposal A: E2-only 分解維持 + S5a/gateway-2 復活 + covering codebook joint-derandomize)**。finding (b): covering source を subtype `{x // 0<P_X x}` に restrict (子計画 settled-facts)。情報側 R_WZ(D) は完成済 (`WynerZiv/` 5 file、0 sorry)。

**SoT / 在庫**: [`wyner-ziv-main-inventory.md`](wyner-ziv-main-inventory.md) (§2 提案 statement / §5 achievability 資産 / §6 converse 資産 / §7 self-build 7 項目 / §10 gateway atom)。**構築本体 (`wz_goodCode_exists_of_testChannel`) 専用在庫 (leg 13)**: [`wyner-ziv-achievability-construction-inventory.md`](wyner-ziv-achievability-construction-inventory.md) — ~26 atom verbatim signature (RD covering / SW binning / gateway / asymptotic)、**genuinely absent = 0** (残 sorry は純 composition plumbing)、hypothesis-supply gap 3 (full-support perturbation / i.i.d. ambient bundle / `Nonempty (Fin k)`、全 regularity manufacture、load-bearing でない)、reuse blocker 1 (`tendsto_exp_mul_codebookSize_inv` が `private` → public alias 要) + adapter 1 (`LossyCode`→`WynerZivCode` 橋)。

**再検証** (prose にキャッシュしない): `scripts/sig_view.ts --sorry InformationTheory/Shannon/WynerZiv/*.lean` / `#print axioms <headline>`。

## 進捗

- [x] M0 — API 在庫 (既存 [`wyner-ziv-main-inventory.md`](wyner-ziv-main-inventory.md) で代替) + converse gateway 実証 ✅ (`csiszar_sum_identity_hetero`、sorryAx-free、`ConverseGateway.lean:48`)
- [x] P1 — statement scaffolding ✅ **proof-done sorryAx-free** (`fdbae7f9`)。`WynerZivAchievable` (distortion-only、`@audit:ok`) + pmf↔measure MI 橋 2 本 (`wzMutualInfoXU/YU_eq_mutualInfo`、closed sorry-free)。`wzErrorProb` は predicate 外に (achievability-internal、P3 へ)。`Operational.lean` 全 0 sorry
- [x] P2 — converse **FULLY CLOSED sorry-free + 独立監査 PASS (leg 11)**。converse own-sorry は **ゼロ**、`wyner_ziv_converse` は sorryAx-free (`@audit:ok`)。leg 4-8 で single-letterisation core、leg 9-10 で endpoint own-body/L1/L2/L3、leg 11 で最後の core `wz_support_reduce` を route C (K=`|α|+3`、bare ambient Carathéodory + ① entropy-mixture identity `wzKernelObjective_eq_blockSum`) で genuine closure (詳細 P2 §、commits `bd52bb26`/`06ed9c2d`/`10a4f3f5`/`70b0e3c9`/`e395874a`、監査 `1caa2375`)。✅
- [ ] P3 — achievability body (binning + covering ハイブリッド)。gateway atoms (leg 12) + 3 leaf atoms (leg 14) CLOSED sorry-free。**leg 15: S1/S2/C/E 4 sub-lemma + top-level reduction (E∘BD) を sorry-free closure**。**leg 16: BD steps 1-2 seam を sorry-free closure (`wz_coveringDistortion_reconcile` + `wz_coveringFamily_of_testChannel`、`@audit:ok`、独立監査 ALL-OK `4b7f6441`)**。**leg 17: BD steps 3-7 を S3-S7 sub-lemma へ skeleton 分解** — S3/S4/S4-uniq/S7 def を sorry-free closure + BD body を capstone S6 への own-sorry ゼロ reduction 化 (`400f9308`)、S5a/S5b の under-hyp DEFECT を独立監査で検出→mass+collision 仮説追加で honest 化 (`f6f31b83`、再監査 OK)。S5a body も sorry-free closure (`35941c54`、`@audit:ok`)。**leg 18: S5b crux `wz_codebook_confusion_expectation_le` を sorry-free closure** (`356c8f25` + 監査 `eebd88f5`、`@audit:ok`)。**leg 19: S6→(D)+(B) 分解** (D1 CLOSED / D2 `wz_covering_codeword_sideInfo_mass_le` + (B) `wzIndexBinningMeasure_collision` CLOSED sorry-free)。**leg 20: D3 `wz_perN_covering_binning_code` が false-as-framed 判明** → 子 plan [`wz-binning-covering-plan.md`](wz-binning-covering-plan.md) へ移譲。**子 Leg 0/A/B/C/C.5/C.6 DONE** (`a59e37cb`/`dfdf3e42`/`02ea97d7`/`25629b0a`/`22b64afa`/`fe3d9482`+`90996ed1`、全 sorry-free + 独立監査 PASS): under-hyp 3 軸 (budget δ-split + reconciliation `hd'_eq`/`hqf` + M-axis `M ≤ exp(nR₁)+1` pin) を honest 化、D3 の `@audit:defect` 除去 honest tier-2 復帰。子 Leg D で **G2/A1 (E2-only decomp + lift identity) `@audit:ok` + A2 `wz_ideal_expectation_eq_covering` sorry-free (`84393413`、finite-sum marginalization、独立監査は Leg E closure 時に A3 と comprehensive)**。**だが Leg D で第4軸 = covering-acceptance C2 を発見・独立監査 CONFIRMED**: E2 = E2b(confusion)∪C2(acceptance) で A3 `wz_exists_binning_E2_bound` (Achievability.lean:3022) が C2 を bound する仮説を欠き false-as-framed (`@audit:defect(false-statement)`、反例 all-atypical-image codebook)。**残 literal sorry 1 = A3 のみ**。次 = 子 Leg E (covering-acceptance C2 再設計 Proposal A: E2-only 分解維持 + S5a/gateway-2 復活 + covering codebook joint-derandomize) 🚧
- [ ] PV — verify (`#print axioms` sorryAx-free + 独立 honesty 監査 + root 配線) 📋

## ゴール / Approach

### Goal (最終定理 signature、inventory §2 を SoT)

i.i.d. source `Measure.pi (fun _ ↦ P_XY)`、decoder side-info `Y^n`。operational headline は reshape 後の rate `wynerZivRate` (= 全有限補助 alphabet `Fin k` 上の feasible factorizable 点にわたる objective の `sInf`、union-of-images 形、`FactorizableRate.lean:636`) を目標にする。二つの operational headline:

```lean
-- pmf 引数は `fun p ↦ P_XY.real {p}` (in-project に `Measure.pmf` 不在)、d は `fun a b ↦ (d a b : ℝ)`。
-- reshape (4532bd48) 後、両 headline とも `wynerZivRate` を目標: 補助 alphabet を固定せず全 `Fin k` の
-- inf をとるため、旧 sizing 前提 hU_card は不要 (下記「reshape の意味」)。
theorem wyner_ziv_achievability
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    -- feasibility / well-posedness guard (achievability only): rules out the
    -- infeasible regime (e.g. D<0 → wzRateValueSet empty → wynerZivRate = sInf ∅ = 0),
    -- where h_rate degenerates to 0<R while WynerZivAchievable is false. The converse
    -- is vacuous in that regime, so it needs no such guard.
    (h_ne : (wzRateValueSet (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D).Nonempty)
    (h_rate : wynerZivRate (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D < R) :
    WynerZivAchievable P_XY d R D

theorem wyner_ziv_converse
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (h_ach : WynerZivAchievable P_XY d R D) :
    wynerZivRate (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D ≤ R
```

**reshape の意味 (旧 `hU_card` を根本から不要化、commit `4532bd48`、historical)**: 旧 framing は converse を **単一固定** 補助 alphabet `U` 上の rate `wynerZivRateFactorizable U` に対して立てていた。この `sInf` は `|U|` に antitone ゆえ、Carathéodory 閾値 `|α|+2` を下回る小さい `U` では inf が achievable `R` より真に上に制限され、**`∀ U` は false-as-framed** だった (旧回避策 = sizing 前提 `hU_card : |α|+2 ≤ |U|` + converse critical path 上の Carathéodory support 補題)。reshape は目標を **全有限補助 alphabet にわたる infimum** `wynerZivRate` に置き換える: 大きな single-letterisation auxiliary (任意有限型) が `wynerZivRate_le_of_feasible` (`FactorizableRate.lean:678`) で直接 feasible 点として着地するため、**false-statement risk が源で消え、sizing precondition は不要 (converse は `∀`-clean)**。achievability も同型に retarget: `wynerZivRate D < R` は inf の定義から良い `U` の存在を与える (∀U achievability が reshape 版を含意、P3 の帰着タスク)。Carathéodory support-reduction は endpoint route の critical path 上 (L1 `wynerZivRate_eq_factorizable_finK` + core `wz_support_reduce`) だが **leg 11 で FULLY CLOSED sorry-free** (route C、K=`|α|+3`、下記 P2)。非退化は `wzObjective_nonneg_of_factorizable` → `wzRateValueSet_bddBelow_of_pmf` が junk `sInf ∅ = 0` を防ぐ。

`WynerZivAchievable P_XY d R D : Prop` = `∃ M, ∃ (c : ∀ n, WynerZivCode (M n) n α β γ), Tendsto rate → R ∧ (誤り確率 → 0 ∧ limsup 歪 ≤ D)` (SW existential の 1-rate 化、inventory §3C)。

### Approach (overall strategy / shape of solution)

WZ operational main = **RD covering (lossy 側) と SW binning (side-info 側) の 2 段ハイブリッド**。両家系の atom は inventory §5/§6 で「reusable as-is」がほぼ全部と確定済 (Mathlib gap ゼロ、すべて in-project)。gap は当初 2 箇所に局在していたが、**converse 側 (i) は leg 11 で FULLY CLOSED**、残るは (ii) **achievability の binning+covering 接着** (§7 #2) のみ。攻略は **converse-first** 順で完遂:

1. **converse は FULLY CLOSED (leg 4-11、sorryAx-free + 独立監査 PASS)**。single-letterisation の真ルートは `Uᵢ=(J,Y_{\i})` + conditional-MI chain (Csiszár `csiszar_sum_identity_hetero` は distortion 側が one-sided aux を禁じるため本ルート orphaned、真 gateway = `iIndepFun → Markov Uᵢ−Xᵢ−Yᵢ` `wz_perletter_markov`、判断ログ #2)。骨格 `rate_distortion_converse_n_letter_singleLetter` (`ConverseNLetter.lean:659`) の antitone+Jensen 段・凸性 (`wynerZivRateFactorizable_convex_in_D`/`_antitone`) は情報側完成品を直呼び、reshape 後 large auxiliary は `wynerZivRate_le_of_feasible` で feasible 点に直接着地。broadcast-channel `bc_input_singleletterize` は不採用。最後の core `wz_support_reduce` (Carathéodory support-reduction) は route C (K=`|α|+3`、bare ambient Carathéodory + entropy-mixture identity) で closure (P2 §)。

2. **achievability は gateway-atom-first で side-info conditional covering を割ってから plumbing**。重心 = **side-info conditional covering** (§10、bin index + `Y^n` から被覆 codeword `U^n` を一意復元する質量下界)。最近接転写元 `conditionalStronglyTypicalSlice_mass_ge` (`ConditionalMethodOfTypes/Mass.lean:1274`) + `conditionalTypicalSlice_card_le` (`SlepianWolf/ConditionalTypicalSlice.lean:140`) は「slice 質量下界」「slice card 上界」を別々に持つが結合形が不在 → **この 1 atom を最初に `lean-implementer` に dispatch** し、通れば achievability 全体が RD covering + SW binning の合成 plumbing で閉じる、通らなければ当該 atom のみ shared sorry に縮退 (撤退ライン)。誤り確率 = covering 失敗 (`encoder_failure_prob_le_exp_neg_M_avg`) + bin 衝突 (`binning_collision_prob`) の和、rate 分解 `R = I(X;U) − I(Y;U)` が 2 指数を分ける。

**依存順序 (skeleton)**: `Basic`/`FactorizableRate`/`ConverseGateway` (完成) → `Operational` (P1 述語 + 橋) → `Converse` (P2、`ConverseGateway` + `Operational` に依存) → `Achievability` (P3、`Operational` + SW binning + RD covering に依存)。

### 型クラス設定 (StandardBorel 訂正を反映、inventory §4 補正後)

```lean
variable {α β γ U : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Fintype γ] [DecidableEq γ] [Nonempty γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
  [Fintype U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]
```

**StandardBorel 訂正 (gateway probe 実測、2026-07-05)**: `#synth` で `StandardBorelSpace` (および tuple 型) が `[Fintype][MeasurableSpace][MeasurableSingletonClass]` から **自動 derive** することを確認 (`[Countable]+[MSC] → [DiscreteMeasurableSpace] → [StandardBorelSpace]` chain が発火)。**明示追加が要るのは `[Nonempty]` のみ**。`condMutualInfo` が両変数に要求する `[StandardBorelSpace X/Y][Nonempty X/Y]` は上記 variable block で充足される。よって inventory §4/§6/§7 の「`[Fintype+MSC]` から StandardBorel は自動導出されない」「`attribute [local instance]` で file 限定発火」という記述は誤りで、**self-build item #6 (local-instance、~10-20 行) とその「instance 忘れが最頻事故」警告は MOOT**。本計画に local-instance サブタスクは置かない。実証: `csiszar_sum_identity_hetero` (`ConverseGateway.lean:48`) は α/β 両側に上記 variable block のみで `condMutualInfo` を効かせ 0 sorry で通っている。

## 既存資産の流用 (inventory §5/§6、Mathlib gap ゼロ)

| leg | 流用 atom (file:line) | 用途 |
|---|---|---|
| converse 骨格 | `rate_distortion_converse_n_letter_singleLetter` (`ConverseNLetter.lean:659`) | antitone+Jensen+superadd+DPI 連鎖のクローン元。右辺を `(1/n)∑[I(Xᵢ;Uᵢ)−I(Yᵢ;Uᵢ)]` に置換 |
| ~~converse auxiliary~~ (不採用) | ~~`bc_input_singleletterize`~~ | **rejected**: broadcast-channel の channel single-letterization は premise が別 (channel coding)。WZ は exact `csiszar_sum_identity_hetero` を直接使い channel single-letterization を経由しない |
| ~~converse gateway~~ (本ルート orphaned) | `csiszar_sum_identity_hetero` (`ConverseGateway.lean:48`、**sorryAx-free**) | prefix/suffix unconditional-MI 形が distortion-hostile な one-sided aux を生むため本ルート **orphaned** (sorryAx-free 維持、削除しない、他所で再利用しうる、wall ではない)。訂正後 rate step は conditional-MI chain (Csiszár 経由せず、判断ログ #2) |
| converse gateway (訂正後、未構築) | `wz_perletter_markov` (`iIndepFun → IsMarkovChain Uᵢ−Xᵢ−Yᵢ`) | 真の決定 atom、condDistrib-from-iid、最深 wall リスク (`wz_converse_perletter_witness` sub-lemma #1、in-project 不在を grep 確認) |
| converse feasible 着地 | `wynerZivRate_le_of_feasible` (`FactorizableRate.lean:678`) | reshape 後: 任意有限型 single-letterisation auxiliary を `wynerZivRate` の feasible 点として直接着地 (Carathéodory 不要) |
| converse 凸性/単調 | `wynerZivRateFactorizable_convex_in_D` (`FactorizableRate.lean`) / `_antitone` | Jensen 段・antitone 段は情報側完成品を直呼び |
| achiev covering | `jointTypicalLossyEncoder` / `distortionTypicalSet` / `encoder_failure_prob_le_exp_neg_M_avg` (`AchievabilityJointTypicalEncoder.lean` / `AchievabilityCodebookMatchProbability.lean`) | `U^n` 被覆 encoder + covering 失敗指数 |
| achiev binning | `binningMeasure` (`Binning.lean:62`) / `binning_collision_prob` (`:106`) / `conditionalTypicalSlice` + `_card_le` (`ConditionalTypicalSlice.lean:140`) | bin 割当 + bin 衝突指数 + side-info decode |
| achiev gateway 素材 | `conditionalStronglyTypicalSlice_mass_ge` (`ConditionalMethodOfTypes/Mass.lean:1274`) | side-info 被覆質量下界 (§10 gateway の最近接転写元) |
| statement 転写 | `slepian_wolf_full_rate_region_achievability` (`PairBound.lean:1041`) / `rate_distortion_achievability` (`AchievabilityStrongTypicality.lean:184`) | existential shape (SW) + slack-exposed witness form (RD) |

---

## M0 — API 在庫 + converse gateway 実証 ✅

**proof-log**: no (在庫は既存 inventory で代替、gateway は実証済)

- [x] 在庫調査は [`wyner-ziv-main-inventory.md`](wyner-ziv-main-inventory.md) で完了 (§5 achievability / §6 converse / §7 self-build 7 項目 / §8 Mathlib gap ゼロ / §10 gateway atom)。
- [x] converse gateway `csiszar_sum_identity_hetero` を `lean-implementer` に dispatch → **sorryAx-free で通過** (同型版証明を verbatim port、`ConverseGateway.lean:48`、commit `b780f782`)。これで converse 全体は骨格クローンで閉じる公算が確定 = feasibility CONFIRMED。
- [x] StandardBorel 訂正確認 (`#synth`): item #6 local-instance は MOOT (上記型クラス設定)。

---

## P1 — statement scaffolding (述語 + 誤り確率 + pmf↔measure 橋)

**ファイル**: `InformationTheory/Shannon/WynerZiv/Operational.lean`
**proof-log**: yes (pmf↔measure 橋 #5 は 3 変数拡張で非自明、再開根拠保存)

- [ ] **`wzErrorProb`** (§7 #1): WZ code の再構成誤り確率。SW `swErrorProb` (`Achievability.lean:45`) を side-info decoder 内蔵の WZ code へ写経 (~30-50 行)。
- [ ] **`WynerZivAchievable P_XY d R D : Prop`** (§7 #1): SW `slepian_wolf_full_rate_region_achievability` の existential を **1-rate 化**してクローン (~40-80 行)。歪項は「誤り確率 → 0 **かつ** limsup 歪 ≤ D」の両条件 (SW=error→0、RD=distortion≤D+ε の合成、inventory §7 #1 の落とし穴)。distortion を `Tendsto (𝓝 D)` でなく `limsup ≤ D+ε` にすると converse 側帰着が変わるので、converse の帰着形と整合させて確定。
- [ ] **pmf↔measure R_WZ 橋** (§7 #5、~100-200 行): `klDiv_joint_eq_mutualInfo` (RD `Converse.lean:108`) を WZ 3 変数 (X,Y,U) へ拡張し、`wzMutualInfoXU U q` = `mutualInfo μ X U` / `wzMutualInfoYU U q` = `mutualInfo μ Y U` を同一視。RD の `mutualInfoPmf ↔ mutualInfo` 橋を 3 変数化。**Mathlib-shape-driven**: 橋の結論形は P2 の single-letterization が返す `condMutualInfo`/`mutualInfo` の `.toReal` 形に合わせる (再整形橋を後から書かないため)。

- **依存 in-project decl**: `WynerZiv/Basic.lean:59/73` (`WynerZivCode`/`expectedBlockDistortion`)、`:102–120` (`wzMutualInfoXU/YU`)、`:233` (`wynerZivRatePmf`); SW `Achievability.lean:45`; RD `Converse.lean:108`。
- **gateway atom**: 無し (定義 + 橋)。橋 #5 は非自明だが Mathlib gap ではない。
- **撤退条件**: 述語が `condMutualInfo`/`wynerZivRateFactorizable` の結論形と噛み合わない場合のみ Mathlib-shape-driven 再定義 (CLAUDE.md 第一選択)。橋 #5 が stall した場合のみ当該補題を `sorry + @residual(plan:wyner-ziv-main-plan)`。**load-bearing hyp / `Prop := True` slot 禁止**、`WynerZivAchievable` に証明の核を bundle しない (existential + regularity のみ)。

---

## P2 — converse body (FULLY CLOSED sorry-free + 独立監査 PASS、leg 11) ✅

**ファイル**: `InformationTheory/Shannon/WynerZiv/Converse.lean` (`ConverseGateway` + `FactorizableRate` §10 + `Operational` に依存)
**proof-log**: yes (single-letterization は converse の実体、再開根拠に必須)

**CLOSED**: converse own-sorry は **ゼロ**、`wyner_ziv_converse` は sorryAx-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`、独立監査 `@audit:ok`)。closure chain は下記 1 行に圧縮 (詳細 git):

- **leg 4-8** — single-letterisation core: DPI 非負 / time-sharing 基盤 / headline body / feasible-point landing / witness `wz_converse_perletter_witness` (5 sub-lemma 全)。真ルートは `Uᵢ=(J,Y_{\i})` + conditional-MI chain、真 gateway `iIndepFun → Markov Uᵢ−Xᵢ−Yᵢ` (`wz_perletter_markov`)。Csiszár `csiszar_sum_identity_hetero` は本ルート orphaned (sorryAx-free 維持、削除せず、wall ではない、判断ログ #2)。
- **leg 9-10** — endpoint own-body + L1 `wynerZivRate_eq_factorizable_finK` (genuine `sInf` 等式) + L2 `wynerZivRateFactorizable_right_continuous_le` (kernel-space compactness) + L3 assembly。
- **leg 11** — 最後の core `wz_support_reduce` を **route C** で genuine closure: (a) ① gateway `wzKernelObjective_eq_blockSum` = entropy-mixture identity `wzKernelObjective = (H(X)−H(Y)) + ∑_u block_u` (`bd52bb26`)、(b) target auxiliary size を `Fin (|α|+2)` → `Fin (|α|+3)` に緩和 (honesty-neutral / 非 load-bearing、K は in-file 3 decl のみに出現し headline に不在、大 K は ∃ を緩めるだけ、endpoint は `K ≥ 1` のみ要求) して **bare ambient Carathéodory in ℝ^{|α|+2}** (`card ≤ |α|+3`) を可能化 — route A (hyperplane-finrank、Mathlib 部品未検証) / route B (coord-drop、α 空で破綻) を回避 (`06ed9c2d`)、(c) generic helper `wz_caratheodory_reduce` / `wz_fin_pad_sum` / `wz_sum_reorder3` (`10a4f3f5`)、(d) body 組立 = 質量等式 + `α⊕Bool` encoding + `Sum.elim` mixture + Carathéodory 適用 + `κ'` 再構成 (`70b0e3c9`/`e395874a`)。独立 honesty 監査 6/6 ALL-OK (`1caa2375`、6-decl chain `@audit:ok`)。

geometry の SoT は inventory [`wz-l1-caratheodory-inventory.md`](wz-l1-caratheodory-inventory.md)。route C で K=`|α|+3` に緩和したため tight-cardinality / Fenchel–Eggleston の議論は moot。slug `wz-auxiliary-cardinality-bound` は 1 dispatch で closure 済 (split-out file は起票不要)。

---

## P3 — achievability body (binning + covering ハイブリッド、重心)

**ファイル**: `InformationTheory/Shannon/WynerZiv/Achievability.lean` (`Operational` + SW binning + RD covering に依存)
**proof-log**: yes (2 段ハイブリッドの誤り事象分解 + source-support restriction は本計画最重、再開根拠に必須)

**構築本体 atom SoT**: [`wyner-ziv-achievability-construction-inventory.md`](wyner-ziv-achievability-construction-inventory.md) — ~26 atom verbatim signature (§A-§D)、7-step wiring sketch (§434-475)、genuinely-absent 0。**本節は decomposition/route plan であって atom catalogue ではない** (atom は在庫を参照、重複しない)。

**leg 履歴 (圧縮、詳細 git)**:
- leg 12 — gateway atoms CLOSED sorry-free + 監査 `@audit:ok` (`108ba475`/`72133a7e`): `wz_sideInfo_decoder_confusion_expectation_le:105` (E2 decoder confusion) + `wz_covering_sideInfo_mass_ge:143` (E3 covering acceptance)、既存汎用 atom (`swError_EX_expectation_le` / `conditionalStronglyTypicalSlice_mass_ge`) の直接 instantiation。E1 covering X→U = `encoder_failure_prob_le_exp_neg_M_avg` (α:=X,β:=U)。3 誤り指数すべて既存 in-project atom。
- leg 13 — `wyner_ziv_achievability_codes` を honest 分解: witness 抽出 `wz_testChannel_of_rate_lt:253` CLOSED sorry-free `@audit:ok`、構築本体を単一 sorried `wz_goodCode_exists_of_testChannel` に集約 + feasibility guard `h_ne` で false-as-framed 訂正 (`214ae65a`)。
- leg 14 (`d5194840`) — covering+binning core が消費する **3 leaf atoms を sorry-free で closure** (`@audit:ok`)、new residual なし: `wz_nonempty_of_factorizable:281` (`Nonempty (Fin k)` from row-sum) / `wz_fullKernelSupport_perturbation:311` (feasible `qf` + slack δ → full-support **kernel** `0<κ'` + factorizable + obj<R + dist≤D+δ) / `wz_tendsto_exp_mul_codebookSize_inv:432` (`exp(nc)·codebookSize⁻¹→0`、SW private の public re-proof)。
- leg 15 — **S1/S2/C/E 4 sub-lemma + top-level reduction を sorry-free closure** (`@audit:ok`、独立監査 ALL-OK `0bb1bf38`): (S1) `wz_restrictedCoveringJoint_pos` (`@audit:ok`、独立監査 2026-07-06) / (E) `wz_diagonalize_slack` (general δ-diagonalization `∀δ∃c`→`∃c∀ε`、`Nat.findGreatest` + Archimedean `exists_nat_one_div_lt`、`6925b90a`) / (S2) `wz_expectedBlockDistortion_source_agree` (null-set a.e.-agreement、`measurePreserving_eval` coordinate marginal + `integral_congr_ae`、`a78282a2`) / (C) `wz_covering_lossyCode_exists` (RD slack quintet threading + 新 sorry-free helper `wz_jointStronglyTypical_mem_distortionTypical` = strong→weak typicality bridge、`212f8bd2`)。top-level `wz_goodCode_exists_of_testChannel` は **E∘BD reduction** (body = `wz_diagonalize_slack (wz_perDelta_codes_exist …)`、signature 不変)。残 sorry = (BD) `wz_perDelta_codes_exist` 唯一 (covering+binning giant、~L873)。
- leg 16 — **BD の steps 1-2 seam を sorry-free closure** (`@audit:ok`、独立監査 ALL-OK `4b7f6441`): (reconcile) `wz_coveringDistortion_reconcile` = covering proxy 歪 `d'(⟨x,_⟩,u):=∑_y (P_XY(x,y)/P_X x)·d(x,qf.2(u,y))` (`Real.toNNReal`) と WZ 実歪の恒等式 `expectedDistortionPmf d' qStar = wzExpectedDistortion (Fin k) d q' qf.2` (subtype→full-alphabet 拡張 + P_X zero-atom 消失、`602dab9d`) / (steps 1-2) `wz_coveringFamily_of_testChannel` = feasible `qf` → perturbation (leaf) → subtype restrict (S1) → reconcile → covering LossyCode family (C) を 9 連言存在で package (hyps = `hqf`/`hobj`/`δ` のみ、covering 存在は結論)。BD body は covering family を `obtain` し **steps 3-7** (binning/decoder/3 error exponents/pigeonhole/squeeze) を単一 sorry (L1084) + 精密 7-step map コメントに縮小。**設計判断**: covering family を `∀ R₁ > mutualInfoPmf qStar, ∀ ε'>0, ∃ family` として露出 = rate-split accounting (`mutualInfoPmf qStar = wzMutualInfoXU q'` の MI restriction 恒等式 + `R₁` vs `I(Y;U)` vs `R`) を BD residual (step 3) に defer (clean seam)。**cap 16 到達で PAUSED、steps 3-7 は cap 延長要の heavy leg**。
- leg 17 — **BD steps 3-7 を S3-S7 sub-lemma へ skeleton 分解** (`400f9308`/`f6f31b83`、独立監査 2 pass): (closed sorry-free) S3 `wzCodeOfCoveringBinning` (WZ code = `f∘c₁.encoder` / decoder letterwise `rec`) / S4 `wzBinTypicalDecoder` (bin 限定 `∃!` codebook-member 探索) + `wzBinTypicalDecoder_eq_of_unique` (SW `swJointTypicalDecoder_eq_of_unique` mirror) / S7 `wzLiftSupportCode` (α'→α support lift)。**BD body `wz_perDelta_codes_exist` は own-sorry ゼロの reduction** (covering data を `obtain` → capstone S6 へ `exact`)。**S5a** `wz_covering_failure_prob_le` (E1 covering-failure) は **body も sorry-free closure** (`35941c54`、`@audit:ok`、orchestrator #print axioms 検証: `(1−p)^M₁ ≤ e^{−M₁p}` = `one_sub_pow_le_exp_neg_mul` + `hmass` + `integral_const`、`p_typ≤1` は `Us 0` 可測性なしで sub-probability 経由)。残 sorry 2 = **S5b** `wz_codebook_confusion_expectation_le` (E2 crux = codebook 限定 confusion、body に union-over-M₁ count) / **S6** `wz_perDelta_covering_binning` (steps 3-7 capstone、13 covering-data 仮説は genuine precondition)。両 `@residual(plan:wyner-ziv-main-plan)`。**honesty**: 初版 S5a/S5b は free exponent (`I`/`δ`/`I_YU`) が mass 束縛仮説を欠き under-hypothesized=false-statement (独立監査が DEFECT 検出) → S5a に mass 下界 `∀x, exp(−n(I+δ)) ≤ p_typ x`、S5b に per-codeword mass 上界 `≤ exp(−n·I_YU)` + binning collision `binMeas{f m'=f m}=M⁻¹` (`binning_collision_prob` mirror) を追加し honest 化 (再監査 OK、codebook-restriction count は body に残置=bundling 回避)。
- leg 18 (`356c8f25`/監査 `eebd88f5`) — S5b crux `wz_codebook_confusion_expectation_le:1254` sorry-free closure (`@audit:ok`)、outer-sum-first (biUnion over `m'` → per-`m'` Tonelli swap → `hcollision`+`hmass`)。
- leg 19 — **S6 → (D) + (B) 分解** (`@audit:ok` chain + tier-2 D3): D1 rate-identity `wz_mutualInfo_restriction_eq` CLOSED sorry-free / D2 `wz_covering_codeword_sideInfo_mass_le:1807` CLOSED sorry-free / (B) collision `wzIndexBinningMeasure_collision:1504` CLOSED sorry-free。S6 `wz_perDelta_covering_binning:2224` body は (D) `wz_perDelta_covering_binning_eventual:2142` への sorry-free glue、(D) は rate-split glue で D3 `wz_perN_covering_binning_code:2054` に hand off (D3 = 唯一の残 sorry)。
- leg 20 (commit `b1cb2915`) — **D3 が false-as-framed 判明** (独立監査 OVERTURN、機械確認): exact `≤ D+δ` 結論を `hfeas` が good-event proxy に δ 全額を使い error term 予約ゼロ、反例 `distortionMax d = D+δ+η` (η>0) で `∀n` fail。姉妹定理 `rate_distortion_achievability:184` は `≤ D+ε'` 止まり + 明示 slack `h_slack` (L118/L202) で ε'/2 予約。D3 に `@audit:defect(false-statement)` + `@audit:closed-by-successor(wz-binning-covering)`。**δ-split 修正 + genuine closure を split-out 子 plan [`wz-binning-covering-plan.md`](wz-binning-covering-plan.md) (Leg 0-D) へ移譲**。cause:false-statement (親 #11 under-hyp トラップの family 再発)。

**settled 構造的所見 (b) source-support restriction** は下記 settled-facts に記録 (再導出高コストの構造判定)。要旨: perturbation leaf は full-support **kernel** `0<κ'` を与えるが **(X,U) joint は globally full-support にならない** (`IsWynerZivFactorizable` が XY-marginal を `P_XY` に pin ゆえ `wzMarginalXU q'(x,u)=κ'(x,u)·P_X(x)` は P_X ゼロ atom で消える)。RD covering `rate_distortion_achievability` は GLOBAL `hqStar_pos:∀p,0<qStar p` を hard-require → heavy core は covering source を subtype `α':={x // 0<P_X x}` に restrict する必要 (block distortion は `Measure.pi P_XY` 下で P_X ゼロ atom 到達 sequence にゼロ mass ゆえ WLOG)。leaf docstring `Achievability.lean:487-502` に stall map。

### 構築本体 skeleton (skeleton-driven、E∘BD 分解)

`wz_goodCode_exists_of_testChannel` の top-level body は **E∘BD reduction** (`wz_diagonalize_slack (wz_perDelta_codes_exist …)`) に決着 (leg 15、sorry-free)。**composition boundary = E/BD**: honesty-critical な diagonalization split は E (`wz_diagonalize_slack`: `∀δ∃c`→`∃c∀ε`) と BD (`wz_perDelta_codes_exist`: per-δ 達成) の境界に置く。**S1/S2/C は top-level glue でなく BD の body 内で消費される** — C→S2 glue が term-level `qStar`/`d'` 構成を要し top glue level で sorry 化できないため (leg 15 決定、判断ログ #9)。**全 sub-lemma の撤退口 = `sorry + @residual(plan:wyner-ziv-main-plan)` のみ** (class は `plan` 固定、in-project atom ゆえ `wall` 不可)、mathematical core は body に置き `*Hypothesis`/`*Reduction`/`IsXxxClaim` に bundle しない。残 sorry = (BD) 唯一。

- [x] **(S1) 制限被覆 joint の global full support** — `wz_restrictedCoveringJoint_pos` DONE sorry-free `@audit:ok` (独立監査 2026-07-06)。subtype `α':={x // 0<P_X x}` 上の (X,U) joint を global full-support pmf として構成 (κ'·P_X>0 + row-sum → simplex)。BD の body が consume。
- [x] **(S2) block-distortion source-support WLOG reconciliation** — `wz_expectedBlockDistortion_source_agree` DONE sorry-free (`a78282a2`)。full-support source sequence 上で一致する 2 code は expected distortion が等しい (`Measure.pi P_XY` が P_X ゼロ atom 到達 sequence に zero mass = null-set transport)、`measurePreserving_eval` coordinate marginal + `integral_congr_ae`。α'-code→α-code 延長を可能化、BD が (C) と合成消費。
- [x] **(C) covering layer** — `wz_covering_lossyCode_exists` DONE sorry-free (`212f8bd2`)。α'-restricted global-full-support (X,U) joint に `rate_distortion_achievability` を適用 (RD slack quintet `ε_X ε_join ε_dist δ_kl δ_typ`/`qZ_min` は body 内 construct = 非露出)、`LossyCode` を返す。新 sorry-free helper **`wz_jointStronglyTypical_mem_distortionTypical`** (strong→weak typicality bridge) を追加。BD が consume。distortion-shape 整合 (被覆歪 X↔U proxy `d'` vs WZ 実歪 X↔γ + side-info) は BD に残す load-bearing subtlety。
- [x] **(E) error→0 の全 ε 持ち上げ (diagonalization)** — `wz_diagonalize_slack` DONE sorry-free (`6925b90a`)。general δ-diagonalization `∀δ∃c`→`∃c∀ε` (`Nat.findGreatest` + Archimedean `exists_nat_one_div_lt`)。top-level が **E∘BD** で消費 = per-δ 達成 (BD) を全 ε 到達に持ち上げる。

- [ ] **(BD→D3) covering+binning giant を skeleton 分解済、残 sorry = D3 唯一、closure は子 plan へ移譲**。`wz_perDelta_codes_exist:2284` は leg 17 で sorry-free reduction 化 (covering data を `wz_coveringFamily_of_testChannel:955` から `obtain` → S6 に `exact`)。legs 17-19 で giant を S3 `wzCodeOfCoveringBinning:1056` / S4 `wzBinTypicalDecoder:1072` / S5a `wz_covering_failure_prob_le:1133` / S5b `wz_codebook_confusion_expectation_le:1254` / S6 `wz_perDelta_covering_binning:2224` / S7 `wzLiftSupportCode:1450` / D1 rate-identity / D2 `wz_covering_codeword_sideInfo_mass_le:1807` / (B) `wzIndexBinningMeasure_collision:1504` / gateway 1-2 に分解 — **上記は全て CLOSED sorry-free**。**唯一の残 sorry = D3 `wz_perN_covering_binning_code:2054` (sorry L2082)**、leg 20 で false-as-framed 判明 (`@audit:defect(false-statement)`)。**δ-split 修正 (Leg 0) + genuine closure (Leg A-D) は split-out 子 plan [`wz-binning-covering-plan.md`](wz-binning-covering-plan.md) が SoT** (~800-1500 行、consume atom / two-ambient subtlety / 撤退口の詳細は子 plan)。撤退口 = `sorry + @residual(plan:wz-binning-covering)`。

**最終組立 (leg 15 決着)**: top-level `wz_goodCode_exists_of_testChannel` = **E∘BD** (`wz_diagonalize_slack (wz_perDelta_codes_exist …)`、sorry-free)。BD の body 内で (S1)→(C)(α' 上)→(S2)(α 延長) を合成消費。残 = BD 本体の fill。

- **依存 in-project decl (在庫 §A-§D SoT)**: `RateDistortion/AchievabilityStrongTypicality.lean:184`、`AchievabilityJointTypicalEncoder.lean:63/76/97/109`、`AchievabilityCodebookMatchProbability.lean:63/138`、`AchievabilityAsymptoticFailureDecay.lean:40/78/203`、`AchievabilityAmbientMeasure.lean:139/153/156/165/174/183/216`、`ConditionalMethodOfTypes/Mass.lean:1274`、`SlepianWolf/Binning.lean:62/106`・`ConditionalTypicalSlice.lean:51/140`、`WynerZiv/Basic.lean:73/106/110`、`FactorizableRate.lean:135/233`。
- **予想規模**: (BD) ~800-1500 行 (本計画の重心、唯一の残 sorry、own decomposition 見込み)。
- **撤退条件 (honest、hypothesis bundling 禁止)**:
  1. 各 sub-lemma が stall → 当該 sub-lemma の signature を上記のまま維持し body を **`sorry + @residual(plan:wyner-ziv-main-plan)`** で開ける (leaf 先埋めの skeleton-driven)。covering 下界を `*Hypothesis` predicate に **bundle しない**。
  2. **`wz_goodCode_exists_of_testChannel` の signature に full-support 仮説を追加しない** (crux、判断ログ #9): support-restriction は proof-internal (subtype `α'` 経由) であって missing hypothesis ではない、追加すると load-bearing precondition が caller に移り headline の honesty を壊す。regularity hyp (`IsProbabilityMeasure` / 可測性 / `iIndepFun` / `Nonempty` / uniform message) は precondition で OK。

---

## PV — verify

**proof-log**: no

- [ ] 各ファイル `lake env lean …` silent (sorry warning のみ許容 = type-check done)。
- [ ] proof done 判定: `wyner_ziv_converse` / `wyner_ziv_achievability` が `#print axioms` で sorryAx 非依存 (`[propext, Classical.choice, Quot.sound]`) を機械確認。
- [ ] 新規 `sorry + @residual` 導入 commit があれば **独立 honesty 監査** (`honesty-auditor`) を session 内で起動 (orchestrator-mandatory)。
- [ ] `InformationTheory.lean` に新規 file (Operational → Converse / Achievability) の import を追加 (orchestrator が最後にまとめて)。root 登録 + README Ch.15 表登録は closure 後。

---

## ファイル配置 (既存 `WynerZiv/` 構成を踏襲)

```
InformationTheory/Shannon/WynerZiv/
  Basic.lean                    -- 完成 (WynerZivCode / expectedBlockDistortion / wzMutualInfoXU/YU / wynerZivRatePmf)
  FactorizableRate.lean         -- 完成 (wynerZivRateFactorizable / _antitone / _convex_in_D; §10 reshape: wzRateValueSet / wynerZivRate / wynerZivRate_le_of_feasible)
  ConditionalEntropyConvexity.lean -- 完成 (_unconditional)
  ConverseGateway.lean          -- 完成 (csiszar_sum_identity_hetero、sorryAx-free)
  Operational.lean              -- P1: WynerZivAchievable / wzErrorProb / pmf↔measure 橋
  Converse.lean                 -- P2: single-letterization (ConverseGateway + Operational 依存)
  Achievability.lean            -- P3: binning+covering ハイブリッド (Operational + SW/RD 依存)
```

import 連鎖: `{Basic, FactorizableRate, ConverseGateway}` ← `Operational` ← {`Converse`, `Achievability`}。各実装 agent は `InformationTheory.lean` を編集せず、orchestrator が最後に import をまとめて追加。

---

## 撤退ライン / honesty (集約)

撤退口は **`sorry + @residual(<class>:<slug>)` のみ** (CLAUDE.md「検証の誠実性」)。証明の核を load-bearing `*Hypothesis`/`*Reduction`/`IsXxxClaim` predicate に bundle するのは禁止、`Prop := True` slot 禁止、退化定義悪用禁止。regularity hyp (full-support / `IsProbabilityMeasure` / 可測性 / `iIndepFun` / `Nonempty` / memoryless-Markov) は precondition で OK。

**class 選択 (audit-tags 準拠)**: WZ operational main の gap は **Mathlib gap ではなく in-project atom の未実装**である (inventory §8、operational coding-theory は Mathlib 完全不在だが atom はすべて in-project 実在、合成のみが gap)。よって撤退 class は **`plan`** (in-project self-build の closure planned) を既定とし、`wall` は使わない (audit-tags「壁 = Mathlib 未整備」の語彙に不一致 = 誤分類になる)。候補 slug の対応:

- **本計画内 closure (第一)**: 各 headline body の in-plan 退避 = `@residual(plan:wyner-ziv-main-plan)`。
- **split-out closure plan (第二、leg が独自 plan を要すると判明した場合)**: achievability D3 = `@residual(plan:wz-binning-covering)` — **子 plan [`wz-binning-covering-plan.md`](wz-binning-covering-plan.md) 起票済 (leg 20、ACTIVE)**、D3 の δ-split + closure を Leg 0-D で保持。converse = `@residual(plan:wz-auxiliary-singleletter)` (未起票、converse は既に CLOSED ゆえ不要見込み)。いずれも kebab-case = 新 plan filename stem。
- **wall 昇格 (第三、条件付き)**: side-info conditional covering が in-project atom から **組めない真の Mathlib gap** と gateway-atom-first で判明した場合のみ、shared sorry 補題を後続 PR で audit-tags register の wall (`joint-typicality-multi` 系 or 新 wall) に昇格。既定は plan-slug (audit-tags「提案中 wall」default 方針「plan-slug で揃え、wall 化は後続 PR」)。

**Carathéodory (`wz-auxiliary-cardinality-bound`) は CLOSED (leg 11)**: L1 `wynerZivRate_eq_factorizable_finK` + core `wz_support_reduce` を route C (K=`|α|+3`、bare ambient Carathéodory in ℝ^{|α|+2} + entropy-mixture identity `wzKernelObjective_eq_blockSum`) で genuine closure、`wyner_ziv_converse` は sorryAx-free (`@audit:ok`)。K を `|α|+3` に緩和したのは honesty-neutral / 非 load-bearing (in-file 3 decl のみに出現、headline に不在、endpoint は `K ≥ 1` のみ要求)。slug `wz-auxiliary-cardinality-bound` は 1 dispatch で closure 済 (split-out file 不要)。

## settled-facts (minimal、再導出可能なものは都度 `#print axioms` / `rg`)

- reshape (`4532bd48`): operational headline は `wynerZivRate` (全有限補助 alphabet `Fin k` 上 `sInf`、`FactorizableRate.lean:636`) を目標。固定-`U` framing は小さい `U` で false-as-framed だったが inf-over-all で source から解消 → sizing precondition (旧 hU_card) 不要。Carathéodory support-reduction (`wz_support_reduce`、slug `wz-auxiliary-cardinality-bound`) は endpoint critical path 上だったが **leg 11 で CLOSED** (route C)。非退化は `wzObjective_nonneg_of_factorizable` → `wzRateValueSet_bddBelow_of_pmf` が junk `sInf ∅ = 0` を防止 (confidence: human-judgment、reshape 独立 honesty-audit PASS 2026-07-05)。
- route C: target auxiliary size K = `|α|+3` (bare ambient Carathéodory in ℝ^{|α|+2}、support `card ≤ d+1 = |α|+3`)。当初想定の K = `|α|+2` (tight Fenchel–Eggleston) は Mathlib 不在だったが、K を `|α|+3` に緩めて bare Carathéodory を使う route で回避 (route A hyperplane-finrank / route B coord-drop を不採用)。K は honesty-neutral / 非 load-bearing (in-file 3 decl のみに出現、headline `wyner_ziv_converse` に不在、endpoint は `K ≥ 1` のみ要求、大 K は ∃-claim を緩めるだけ) → headline を weaken しない (confidence: proof-pivot verbatim-verified、監査 PASS)。
- single-letterisation の真ルート = `Uᵢ=(J,Y_{\i})` + conditional-MI chain、真 gateway = `iIndepFun → Markov Uᵢ−Xᵢ−Yᵢ` (`wz_perletter_markov`)。Csiszár `csiszar_sum_identity_hetero` (`ConverseGateway.lean:48`) は distortion 側が one-sided aux を強制するため本ルート **orphaned** (削除せず維持、wall ではない、confidence: human-judgment、proof-pivot consult)。このルートで witness core (sub2/sub3/gateway) は leg 8 で CLOSED (再検証 `#print axioms`、prose にキャッシュしない)。
- **converse own-sorry は ゼロ (leg 11)**: `wyner_ziv_converse` は sorryAx-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`、独立監査 `@audit:ok` `1caa2375`)。closure chain = entropy-mixture identity gateway `wzKernelObjective_eq_blockSum` (`bd52bb26`) + route C (`06ed9c2d`/`10a4f3f5`/`70b0e3c9`/`e395874a`)。再検証は `#print axioms wyner_ziv_converse` (prose にキャッシュしない)。
- Mathlib に operational coding-theory / method-of-types / Csiszár は **完全不在** (loogle `Csiszar`/`rateDistortion`/`WynerZiv`/`typicalSet` = Found 0、confidence loogle-neg)。すべて in-project。→ 撤退 class は `plan` (wall ではない)。
- **source-support restriction (finding (b)、leg 14、再導出高コスト構造判定)**: perturbation は full-support **kernel** `0<κ'` しか与えず、(X,U) joint は globally full-support にならない。`IsWynerZivFactorizable` が XY-marginal を `P_XY` に pin (`FactorizableRate.lean:135`) するため `wzMarginalXU q'(x,u) = ∑_y κ'(x,u)·P_XY(x,y) = κ'(x,u)·P_X(x)` は **P_X のゼロ atom で κ に依らず消える**。RD covering `rate_distortion_achievability` (`AchievabilityStrongTypicality.lean:184`) は GLOBAL `hqStar_pos:∀p,0<qStar p` を hard-require。→ heavy core は covering source を subtype `α':={x // 0<P_X x}` に restrict、globally-full-support (X,U) joint を RD に供給する必要。block distortion は `Measure.pi P_XY` 下で P_X ゼロ atom 到達 sequence にゼロ mass ゆえ `supp(P_X)` restriction は WLOG。RD file 自身が deferred (docstring は "requires a perturbation argument" と flag するが pmf level で止まり pinned XY-marginal に踏み込まない)。confidence: human-judgment (構造判定、leaf docstring `Achievability.lean:487-502` に stall map、機械検証は construction body 完成後)。
- StandardBorel は `[Fintype][MeasurableSpace][MeasurableSingletonClass]` から `#synth` で自動 derive、明示追加は `[Nonempty]` のみ (confidence: machine、`csiszar_sum_identity_hetero` が variable block のみで 0 sorry を実証)。inventory §4/§6/§7 の反対記述 + item #6 は MOOT。

(これ以上のキャッシュはしない。`wyner-ziv-facts.md` は現時点で作らない。)

## 判断ログ

append-only。決着済 entry は削除 (git が履歴)、active のみ残す。≤ 10 entry。

1. **reshape 採択 (proposal A、`4532bd48`、active 決定軸)**: operational headline を固定-`U` rate から **全有限補助 alphabet 上 inf** `wynerZivRate` (`FactorizableRate.lean:636`) に retarget。旧固定-`U` は小さい `U` で false-as-framed (sInf が `|U|` に antitone) ゆえ `hU_card` sizing 前提を撤去 (converse は `∀`-clean)、large single-letterisation auxiliary は `wynerZivRate_le_of_feasible:678` で feasible 点に着地。非退化は `wzObjective_nonneg_of_factorizable`→`wzRateValueSet_bddBelow_of_pmf` が junk `sInf∅=0` を防止。詳細 settled-facts。
2. **single-letterisation の真ルート (proof-pivot consult、番号凍結 = 親参照)**: distortion 側 (`X̂ᵢ=decoder(J,Yⁿ)ᵢ` が `Yⁿ` 全体依存) が one-sided aux `Uᵢ=(J,Y^{i-1})` を禁じ `Uᵢ=(J,Y_{\i})` を強制 → Csiszár `csiszar_sum_identity_hetero` は本ルート **orphaned** (削除せず維持、wall ではない)、rate step は conditional-MI chain。真 gateway = `iIndepFun → Markov Uᵢ−Xᵢ−Yᵢ` (`wz_perletter_markov`)。このルートで witness core を leg 8 で CLOSED (sorryAx-free + 独立監査 PASS)。
4. **撤退 class = `plan` (wall ではない、active 決定軸)**: WZ gap は Mathlib gap でなく in-project atom 合成の未実装 (inventory §8)。既定退避 = `@residual(plan:wyner-ziv-main-plan)`、split-out は `wz-binning-covering`/`wz-auxiliary-singleletter`。wall 昇格は side-info covering が真の Mathlib gap と gateway-atom-first で判明した場合のみ後続 PR で。
5. **親再開の注記 (active)**: 親 [`wyner-ziv-moonshot-plan.md`](wyner-ziv-moonshot-plan.md) は ACTIVE (情報側完成 record 保存)。textbook-roadmap Ch.15 の「WZ main scope-out」行は **closure まで維持** (attack ≠ scope 再開の確定、roadmap は本 planner の editing boundary 外)。
9. **P3 construction: E∘BD composition-boundary + full-support 不追加 crux (leg 15、active、本線)**: top-level `wz_goodCode_exists_of_testChannel` は **E∘BD reduction** (`wz_diagonalize_slack (wz_perDelta_codes_exist …)`、sorry-free、signature 不変) に決着。**composition-boundary 決定 (leg 15)**: honesty-critical な diagonalization split は E/BD 境界に置き、**S1/S2/C は top-level glue でなく BD の body 内で消費**する — C→S2 glue が term-level `qStar`/`d'` 構成を要し top glue level で sorry 化できないため。leg 15 で S1/S2/C/E 4 sub-lemma + reduction を sorry-free closure (`@audit:ok`、独立監査 ALL-OK `0bb1bf38`)、残 sorry = (BD) `wz_perDelta_codes_exist` 唯一。**crux (leg 13 由来、凍結)**: `wz_goodCode_exists_of_testChannel` の signature に **full-support 仮説を追加しない** — support-restriction は proof-internal (subtype α' 経由、BD body 内) であって missing hypothesis ではない (RD unconditional 版に対応)、追加すると load-bearing precondition が caller に移り headline honesty を壊す (leg 15 top-level reduction が signature 不変で維持を confirm、独立監査 confirmed)。finding (b) source-support は settled-facts。
10. **E2 = codebook 限定 confusion が WZ の真の核 (leg 16 finding、leg 17-18 で settled、子 plan Leg C が参照)**: gateway-1 は `swError_EX` 由来で SW 指数 `H(U|Y)` (全系列) を返し WZ rate `I(X;U)−I(Y;U)` では E2 を消せない (noisy test channel で `H(U|X)>0`)。WZ を SW と分ける真の核 = codebook 限定 confusion `wz_codebook_confusion_expectation_le:1254` — leg 17-18 で **CLOSED sorry-free** (`@audit:ok`)。子 plan `wz-binning-covering` Leg C がこの閉じた atom を消費 (再証明しない)。
11. **P3 skeleton sub-lemma の under-hypothesization トラップ (leg 17、独立監査で捕捉、family 再発トラップ)**: BD steps 3-7 の error-exponent sub-lemma を skeleton 化する際、exponent を **free real パラメータ** (`I`/`δ`/`I_YU`) で置き対応する mass 束縛仮説を signature に threading し忘れると、極端値 (`I→−∞`、`I_YU→+∞` 等で RHS→0) で LHS(確率∈[0,1]) を下回り **stated bound が偽 = false-statement DEFECT** になる (S5a/S5b 初版が該当、独立監査が退化境界 `p_typ≡0`/`M=1` で refute)。**正しい形**: exponent の値を pin する **derived-precondition** を明示仮説にする — S5a は mass 下界 `∀x, exp(−n(I+δ)) ≤ p_typ x` (covering-acceptance AEP、`wz_covering_sideInfo_mass_ge` が供給)、S5b は per-codeword mass 上界 `≤ exp(−n·I_YU)` (codeword×Y^n AEP) + binning collision `binMeas{f m'=f m}=M⁻¹` (`binning_collision_prob` mirror)。これらは reusable atomic precondition (SW `swError_EX_expectation_le` が同型入力を消費) であって **load-bearing でない** — codebook-restriction の union-over-M₁ count は結論 set-builder + body に残る。`wynerZivRate_nonneg` docstring が既に同型 under-hyp を対比参照しており **family 再発トラップ**として記録 (free-exponent sub-lemma は必ず mass-bound 仮説を同伴させる)。**4 度目 (leg 20+、第4軸 covering-acceptance C2)**: under-hyp は明示 param でも ∃-witness でもなく **conclusion の sub-event 内 (C2 ⊂ E2)** に潜みうる = free-exponent トラップの sub-event 形。教訓拡張 = error-event atom を event-label 類似で dead-judge せず conclusion の集合所属述語で検証、under-hyp は param / ∃-witness / **sub-event** の 3 所に潜む (子計画 判断ログ #6)。
12. **D3 の under-hyp を子 plan で段階的に honest 化、残 literal sorry 1 = A3 (leg 20 発見 → 子 Leg 0/C.5/C.6/E、active)**: D3 `wz_perN_covering_binning_code` の exact `≤ D+δ` は当初 under-hypothesized で false-as-framed。子 plan [`wz-binning-covering-plan.md`](wz-binning-covering-plan.md) で under-hyp 3 軸を honest 化済 — 軸1 budget (δ-split、`hfeas`/`hcov₁` を `D+δ/2` に締め `δ/2` 予約、Leg 0 `a59e37cb`)、軸2 reconciliation (`hd'_eq`+`hqf` threading、Leg C.5 `22b64afa`)、軸3 M-axis (`hcov₁` に `M ≤ exp(nR₁)+1` pin、Leg C.6 `fe3d9482`/`90996ed1`、独立監査 all-PASS)、いずれも caller discharge の非 bundling precondition-exposure。**D3 body は sorry-free reduction に復帰 (M-axis defect 除去 honest tier-2)、A2 `wz_ideal_expectation_eq_covering` も sorry-free (`84393413`)**。**だが子 Leg D で第4軸 = covering-acceptance C2 を発見・独立監査 CONFIRMED**: E2 = E2b(confusion)∪C2(acceptance) (回復に acceptance 要求 `wzBinTypicalDecoder_eq_of_unique` ゆえ C2 ⊂ E2) で A3 `wz_exists_binning_E2_bound` (Achievability.lean:3022) が C2 を bound する仮説を欠き false-as-framed (反例 all-atypical-image codebook)。**残 literal sorry 1 = A3 のみ**、`@audit:defect(false-statement)`。子 Leg E (covering-acceptance 再設計 Proposal A: E2-only 分解維持 + S5a/gateway-2 復活 + covering codebook joint-derandomize、Leg C.6 同型 precondition-exposure で hcov₁ に acceptance-failure bound conjunct 追加) で closure。**Leg E first move (署名 ripple `b5b22385`) は独立監査で DEFECT** (`d71b9dfb`): (i) `hcov_accept` の free `∃ ε` が vacuous (huge-ε で fail set ∅)、(ii) **第5軸 = dα'-d scaling** (tolerance が `distortionMax d`・結論が `distortionMax dα'`)。rework = pinned-ε 形 + dα'-d reconciliation precondition (子計画 判断ログ #7)。cause:false-statement (子 Leg E rework で解消予定)。
