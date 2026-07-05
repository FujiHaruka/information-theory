# Wyner–Ziv operational main theorem (achievability + converse) サブ計画

> **Parent**: [`wyner-ziv-moonshot-plan.md`](wyner-ziv-moonshot-plan.md) §operational main relay

**Status**: ACTIVE 🚧 — **converse single-letterisation core CLOSED (leg 8) + 左端点右連続 endpoint own-body + L2/L3 CLOSED sorry-free (leg 9、独立監査 PASS)**。single-letterisation core 3 decl は leg 9 で `@audit:ok` へ移行 (sorryAx-free 機械確認)。**残 converse own-sorry は 1 本 = L1 Carathéodory `wynerZivRate_eq_factorizable_finK` (`Converse.lean` ~:1975、`@residual(plan:wz-auxiliary-cardinality-bound)`)** — endpoint を完全 close する最後の crux。Goal の残り = **L1 Carathéodory + achievability P3 (未着手)**。operational code ↔ R_WZ(D) を繋ぐ **achievability + converse** (Cover–Thomas Thm 15.9.1) を genuine closure する。情報側 R_WZ(D) は完成済 (`WynerZiv/` 5 file、0 sorry)。

**SoT / 在庫**: [`wyner-ziv-main-inventory.md`](wyner-ziv-main-inventory.md) (§2 提案 statement / §5 achievability 資産 / §6 converse 資産 / §7 self-build 7 項目 / §10 gateway atom)。

**再検証** (prose にキャッシュしない): `scripts/sig_view.ts --sorry InformationTheory/Shannon/WynerZiv/*.lean` / `#print axioms <headline>`。

## 進捗

- [x] M0 — API 在庫 (既存 [`wyner-ziv-main-inventory.md`](wyner-ziv-main-inventory.md) で代替) + converse gateway 実証 ✅ (`csiszar_sum_identity_hetero`、sorryAx-free、`ConverseGateway.lean:48`)
- [x] P1 — statement scaffolding ✅ **proof-done sorryAx-free** (`fdbae7f9`)。`WynerZivAchievable` (distortion-only、`@audit:ok`) + pmf↔measure MI 橋 2 本 (`wzMutualInfoXU/YU_eq_mutualInfo`、closed sorry-free)。`wzErrorProb` は predicate 外に (achievability-internal、P3 へ)。`Operational.lean` 全 0 sorry
- [~] P2 — converse **single-letterisation core CLOSED (leg 8)、残 own-sorry 1 本 = 左端点右連続**。両 headline (`wyner_ziv_converse` + 中間 `wyner_ziv_converse_n_letter_singleLetter`) は `wynerZivRate` に retarget 済。**leg 4-8 で genuine closure (sorryAx-free + 独立監査 PASS)**: DPI 非負 `wzObjective_nonneg_of_factorizable`、time-sharing 基盤 (`wzRateValueSet_timeShare_mem`/`_avg_mem` [`FactorizableRate.lean:1230`]/`_weightedSum_mem` [:1162]/`wynerZivRate_convex_in_D`)、headline body、feasible-point landing `wz_converse_feasible_point`、**single-letterisation witness `wz_converse_perletter_witness` の 5 sub-lemma 全** (sub2 `wz_perletter_factorizable` `95f4abc5`/`321abbc6`、sub3 `wz_singleletter_rate_le` + 新 atom `wz_inputs_cond_indep` `72a9077e`/`021d7732`、gateway `wz_perletter_markov` `4eb1a788`)。**leg 9: endpoint own-body + L2 (fixed-K 右連続、kernel-space compactness) + L3 (assembly) を sorry-free に closure、残 own-sorry = L1 Carathéodory `wynerZivRate_eq_factorizable_finK` 1 本のみ** (`@residual(plan:wz-auxiliary-cardinality-bound)`、下記 route)。🚧
- [ ] P3 — achievability body (binning + covering ハイブリッド、**Goal の残り半分、未着手**) 📋
- [ ] PV — verify (`#print axioms` sorryAx-free + 独立 honesty 監査 + root 配線) 📋
- [~] **endpoint `wynerZivRate_le_of_forall_pos_add_endpoint` の L1/L2/L3 route**: leg 9 で **L2+L3+endpoint own-body CLOSED sorry-free** (独立監査 PASS)。残 = **L1 Carathéodory `wynerZivRate_eq_factorizable_finK` (`@residual(plan:wz-auxiliary-cardinality-bound)`)** のみ。headline case C から**のみ** consume = transitively load-bearing (permanent scope-out 不可)。次 leg は **L1 Carathéodory 本体を gateway-atom-first dispatch** (停滞なら split-out plan `wz-auxiliary-cardinality-bound.md` 起票 + 設計先行)

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
    (h_rate : wynerZivRate (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D < R) :
    WynerZivAchievable P_XY d R D

theorem wyner_ziv_converse
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (h_ach : WynerZivAchievable P_XY d R D) :
    wynerZivRate (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D ≤ R
```

**reshape の意味 (旧 `hU_card` を根本から不要化、commit `4532bd48`、historical)**: 旧 framing は converse を **単一固定** 補助 alphabet `U` 上の rate `wynerZivRateFactorizable U` に対して立てていた。この `sInf` は `|U|` に antitone ゆえ、Carathéodory 閾値 `|α|+1` を下回る小さい `U` では inf が achievable `R` より真に上に制限され、**`∀ U` は false-as-framed** だった (旧回避策 = sizing 前提 `hU_card : |α|+1 ≤ |U|` + converse critical path 上の Carathéodory support 補題)。reshape は目標を **全有限補助 alphabet にわたる infimum** `wynerZivRate` に置き換える: 大きな single-letterisation auxiliary (任意有限型) が `wynerZivRate_le_of_feasible` (`FactorizableRate.lean:678`) で直接 feasible 点として着地するため、**false-statement risk が源で消え、sizing precondition は不要 (converse は `∀`-clean)**。achievability も同型に retarget: `wynerZivRate D < R` は inf の定義から良い `U` の存在を与える (∀U achievability が reshape 版を含意、P3 の帰着タスク)。Carathéodory は critical path から外れ、`wynerZivRate = wynerZivRateFactorizable (Fin (|α|+1))` の equivalence は **別の cosmetic 定理** に降格 (下記 deferred)。非退化は `wzObjective_nonneg_of_factorizable` → `wzRateValueSet_bddBelow_of_pmf` が junk `sInf ∅ = 0` を防ぐ。

`WynerZivAchievable P_XY d R D : Prop` = `∃ M, ∃ (c : ∀ n, WynerZivCode (M n) n α β γ), Tendsto rate → R ∧ (誤り確率 → 0 ∧ limsup 歪 ≤ D)` (SW existential の 1-rate 化、inventory §3C)。

### Approach (overall strategy / shape of solution)

WZ operational main = **RD covering (lossy 側) と SW binning (side-info 側) の 2 段ハイブリッド**。両家系の atom は inventory §5/§6 で「reusable as-is」がほぼ全部と確定済 (Mathlib gap ゼロ、すべて in-project)。gap は 2 箇所に局在: (i) **converse の single-letterisation witness (auxiliary `Uᵢ:=(J,Y_{\i})` + Markov-from-iid gateway)** (§7 #3、下記訂正)、(ii) **achievability の binning+covering 接着** (§7 #2)。攻略は **converse-first** 順 (converse は headline + landing まで sorry-free、残は witness 1 本):

1. **converse single-letterisation core は CLOSED (leg 4-8、sorryAx-free + 独立監査 PASS)、残 converse own-sorry は左端点右連続 1 本のみ**。真ルートは `Uᵢ=(J,Y_{\i})` + conditional-MI chain (Csiszár `csiszar_sum_identity_hetero` は distortion 側が one-sided aux を禁じるため本ルート orphaned、真 gateway = `iIndepFun → Markov Uᵢ−Xᵢ−Yᵢ` `wz_perletter_markov`、判断ログ #2)。骨格 `rate_distortion_converse_n_letter_singleLetter` (`ConverseNLetter.lean:659`) の antitone+Jensen 段・凸性 (`wynerZivRateFactorizable_convex_in_D`/`_antitone`) は情報側完成品を直呼び、reshape 後 large auxiliary は `wynerZivRate_le_of_feasible` で feasible 点に直接着地 (Carathéodory sizing 不要)。broadcast-channel `bc_input_singleletterize` は不採用。**残る real gap = 左端点右連続 `wynerZivRate_le_of_forall_pos_add_endpoint` (Carathéodory route L1/L2/L3、P2)**。

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

## P2 — converse body (single-letterisation core + endpoint scaffold CLOSED、残 own-sorry 1 本 = L1 Carathéodory)

**ファイル**: `InformationTheory/Shannon/WynerZiv/Converse.lean` (`ConverseGateway` + `FactorizableRate` §10 + `Operational` に依存)
**proof-log**: yes (single-letterization は converse の実体、再開根拠に必須)

reshape (`4532bd48`) で両 headline を `wynerZivRate` に retarget 済、`hU_card` は不要。leg 4-8 で **DPI 非負 / n-ary time-sharing 基盤 / headline body / feasible-point landing / single-letterisation witness `wz_converse_perletter_witness` (5 sub-lemma 全) をすべて sorry-free に closure** (sorryAx-free + 独立監査 PASS)。**残 own-sorry は 1 本** (`@residual(plan:wyner-ziv-main-plan)`、再検証 `scripts/sig_view.ts --sorry InformationTheory/Shannon/WynerZiv/Converse.lean`):

- [x] **endpoint `wynerZivRate_le_of_forall_pos_add_endpoint` own-body CLOSED (leg 9、sorry-free assembly)** + **L2 `wynerZivRateFactorizable_right_continuous_le` CLOSED** (kernel-space compactness、Cantor FIP + argmin-decoder)。headline case C から**のみ** consume。
- [ ] **(残 sorry) L1 `wynerZivRate_eq_factorizable_finK`** (`Converse.lean` ~:1975、`@residual(plan:wz-auxiliary-cardinality-bound)`): `wynerZivRate = wynerZivRateFactorizable (Fin (|α|+1))`。Carathéodory auxiliary-cardinality bound。endpoint を完全 close する最後の crux。**L1 route は下記。**
- [x] **CLOSED (leg 4-8、sorryAx-free)**: headline `wyner_ziv_converse` body + `wz_converse_feasible_point` landing + **witness `wz_converse_perletter_witness` の 5 sub-lemma 全**。single-letterisation の真ルート = `Uᵢ=(J,Y_{\i})` + conditional-MI chain (真 gateway = `iIndepFun → Markov Uᵢ−Xᵢ−Yᵢ` `wz_perletter_markov` `4eb1a788`、Csiszár `csiszar_sum_identity_hetero` は本ルート orphaned = sorryAx-free 維持・削除せず・wall ではない、判断ログ #2)。sub2 `wz_perletter_factorizable` (`95f4abc5`/`321abbc6`)、sub3 `wz_singleletter_rate_le` + 新 atom `wz_inputs_cond_indep` (`72a9077e`/`021d7732`)、sub4 distortion-avg + assembly。再検証は `#print axioms` (prose にキャッシュしない)。

### 残: 左端点右連続 `wynerZivRate_le_of_forall_pos_add_endpoint` の L1/L2/L3 route (leg 8 proof-pivot-advisor)

proof-pivot-advisor は **大型 self-build** と判定 (quick win 不可、安価な単調極限ルートは minimax 障害で証明的にブロック)。3 分解 (leg 9 で L2/L3 CLOSED、残 L1):

- **L1 (crux、残 sorry)**: 固定-K rate 同定 `wynerZivRate = wynerZivRateFactorizable (Fin K)` (K=|α|+1、**⚠ leg 9 で `wynerZivRatePmf` でなく `wynerZivRateFactorizable` = 同一 factorizable 制約族と確定**)、**Carathéodory auxiliary-cardinality bound**。slug **`wz-auxiliary-cardinality-bound`**、~200-400 行、**HIGH risk**。両包含とも Carathéodory を要す (`sInf ∅=0` collapse ゆえ ≤ 方向も自明でない: S_K≠∅ 保証が要、≥ が reduction 本体)。本体 = Mathlib `Analysis/Convex/Caratheodory` (`Finset.convexHull_eq`/`Finset.mem_convexHull`/`Finset.centerMass_mem_convexHull`) を WZ objective に配線、in-project 類似なし。`wynerZivRate_eq_factorizable_finK` (`Converse.lean` ~:1975) として isolate 済。
- **L2 ✅ CLOSED (leg 9、sorry-free)**: `wynerZivRateFactorizable_right_continuous_le`。scout の subsequence route でなく **kernel(κ)-space compactness** で構築 (feasible kernel = 標準単体の直積 `isCompact_univ_pi`、q-space の存在射影閉性を回避)。Cantor FIP `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` + argmin-decoder `Finite.exists_min`。bridge `wynerZivRateFactorizable_eq_sInf_kernel` が rate↔kernel を橋渡し。support scaffold: `wzJointOfKernel`/`wzKernelSet`/`wzKernelFeasible` + 8 continuity/compactness/closedness 補題 (全 `Converse.lean`、leg 9 追加、sorry-free)。
- **L3 ✅ CLOSED (leg 9、sorry-free)**: endpoint own-body assembly。unused-hyp (`h_ne`/`h_endpoint`) 保持は honest (より弱い仮定で証明 = 非 load-bearing、`set_option linter.unusedVariables false in` scoped、監査 PASS)。

**攻略順序 (gateway-atom-first)**: leg 9 で L1 停滞 → **Proposal B 実施済** (L1 isolate + L2/L3 sorry-free closure、残差を crux 1 点に narrowing)。次 leg は **L1 Carathéodory 本体を gateway-atom-first dispatch**。停滞持続なら split-out plan `wz-auxiliary-cardinality-bound.md` (kebab-case、slug 一致) を起票し設計 (convex-hull ambient / vector map u↦v_u / reduction sub-lemma / kernel 再構成) を先行。auxiliary sizing を `*Hypothesis`/`*Reduction` に **bundle しない** (tier-5 禁止)。regularity hyp (`stdSimplex` / `Nonempty` / `BddBelow`) は precondition で OK。

**罠**: `rg cardinality` の ChannelCoding/Fano/method-of-types hit は全て `log|set|` entropy bound で false-positive (convex-hull support-size とは別物)。keyword でなく **conclusion-shape で照合**。

- **依存 in-project decl**: `FactorizableRate.lean:636` (`wynerZivRate`) / `FactorizableRate.lean:382` (`wynerZivRateFactorizable`、L1 の fixed-K 対象)、`Basic.lean:159` (`continuous_wzObjective`)、`Converse.lean` L1/L2/L3 helper 群 (leg 9 追加)、endpoint consumer = headline case C。
- **gateway atom**: L1 (Carathéodory auxiliary-cardinality bound)。
- **撤退条件 (honest、hypothesis bundling 禁止)**: L1 stall → **L1 単独**に `sorry + @residual(plan:wz-auxiliary-cardinality-bound)`、L2+L3 はその signature の上に build。auxiliary sizing を `*Hypothesis`/`*Reduction` predicate に **bundle しない** (tier-5 禁止)。regularity hyp (`stdSimplex` membership / `IsProbabilityMeasure` / 可測性 / `Nonempty`) は precondition で OK。

---

## P3 — achievability body (binning + covering ハイブリッド、重心)

**ファイル**: `InformationTheory/Shannon/WynerZiv/Achievability.lean` (`Operational` + SW binning + RD covering に依存)
**proof-log**: yes (2 段ハイブリッドの誤り事象分解は本計画最重、再開根拠に必須)

証明 chain (inventory §2 の 1→5):

- [ ] **gateway atom = side-info conditional covering** (§10、~300-500 行): 「covering 済 `U^n` が bin 内で `Y`-conditional に一意復元される」質量下界。`conditionalStronglyTypicalSlice_mass_ge` (`Mass.lean:1274`) + `conditionalTypicalSlice_card_le` (`ConditionalTypicalSlice.lean:140`) の合成 + 誤り事象の和集合上界。**まず `lean-implementer` に本 atom 1 本を dispatch** (gateway-atom-first)。通るか否かが achievability genuine-closure 可否の決定打。検証観点: RD covering 指数 (`encoder_failure_prob_le_exp_neg_M_avg`) と SW bin 衝突指数 (`binning_collision_prob`) が同じ n スケールで両立するか (rate split `R = I(X;U)−I(Y;U)` が 2 指数を分ける)。
- [ ] **step 1-2 (encoder)**: `X^n` を `jointTypicalLossyEncoder` で `U^n` 被覆 → `binningMeasure` で bin 化 (rate 削減)。
- [ ] **step 3-4 (decoder)**: (bin index, `Y^n`) から `conditionalTypicalSlice` で `U^n` 復元 → `f(U,Y)` 再構成、`blockDistortion_le_of_mem_distortionTypicalSet` で歪 ≤ D+ε。
- [ ] **step 5 (誤り→0)**: covering 失敗 (RD 指数) + bin 衝突 (SW 指数) の和 → 0。`ceil_exp_mul_exp_neg_tendsto_atTop` / `exp_neg_tendsto_zero_of_tendsto_atTop` (`AchievabilityAsymptoticFailureDecay.lean`)。
- [ ] **headline `wyner_ziv_achievability`**: `h_rate < R` → 全項 → 0 → `WynerZivAchievable`。codebook 平均 → 存在抽出 `exists_codebook_low_avg` (`AchievabilityCodebookMatchProbability.lean:138`)。

- **依存 in-project decl**: `AchievabilityJointTypicalEncoder.lean:63/97/109`; `AchievabilityCodebookMatchProbability.lean:63/138`; `AchievabilityAsymptoticFailureDecay.lean:40/78/203`; `ConditionalMethodOfTypes/Mass.lean:1274`; `SlepianWolf/Binning.lean:62/106`、`ConditionalTypicalSlice.lean:51/140`; P1 の `WynerZivAchievable`/`wzErrorProb`。
- **gateway atom**: `side-info conditional covering`。通れば RD covering + SW binning の合成 plumbing で連鎖、通らなければ当該 atom のみ shared sorry に縮退。
- **予想規模**: ~800-1500 行 (本計画の重心、唯一の重い合成 gap)。
- **撤退条件 (honest、多段、hypothesis bundling 禁止)**:
  1. gateway atom (side-info conditional covering) が stall → 当該 atom のみ **`sorry + @residual(plan:wz-binning-covering)`** (shared sorry 補題、split-out closure plan slug) で開け、headline は直呼び。covering 下界を `*Hypothesis` predicate に **bundle しない** (旧 scaffold の `IsMACPerEventAEPDecay` 型 primitive bundle 踏襲禁止)。
  2. さらに stall → **full-support + factorizable + `U` Fintype 引数固定** の witness form まで縮退 (RD `rate_distortion_achievability` の slack-exposed 形と同格、inventory §9)。cardinality bound (#7) は最初から別 plan。
  3. headline body 全体を退避する場合は **`sorry + @residual(plan:wyner-ziv-main-plan)`** (本計画内 closure)。regularity hyp (full-support `h_pos` / `IsProbabilityMeasure` / 可測性 / `iIndepFun` / uniform message) は precondition で OK。

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
- **split-out closure plan (第二、leg が独自 plan を要すると判明した場合)**: achievability = `@residual(plan:wz-binning-covering)` / converse = `@residual(plan:wz-auxiliary-singleletter)` (いずれも kebab-case、新 plan filename stem)。
- **wall 昇格 (第三、条件付き)**: side-info conditional covering が in-project atom から **組めない真の Mathlib gap** と gateway-atom-first で判明した場合のみ、shared sorry 補題を後続 PR で audit-tags register の wall (`joint-typicality-multi` 系 or 新 wall) に昇格。既定は plan-slug (audit-tags「提案中 wall」default 方針「plan-slug で揃え、wall 化は後続 PR」)。

**Carathéodory (`wz-auxiliary-cardinality-bound`) は critical path 上 (leg 5 で再浮上)**: 固定-K rate 同定 `wynerZivRate = wynerZivRatePmf (Fin K)` (K=|α|+1) の Carathéodory auxiliary-cardinality bound は、reshape 直後は cosmetic に降格していたが、左端点右連続 `wynerZivRate_le_of_forall_pos_add_endpoint` (`Converse.lean:1773`) の **L1 crux** として critical path に戻った (P2、endpoint route)。L1 stall 時のみ split-out plan `wz-auxiliary-cardinality-bound.md` (kebab-case、slug と一致) を起票し L1 を isolate。現時点では file 不要 (endpoint own-body 内で closure 試行が第一)。

## settled-facts (minimal、再導出可能なものは都度 `#print axioms` / `rg`)

- reshape (`4532bd48`): operational headline は `wynerZivRate` (全有限補助 alphabet `Fin k` 上 `sInf`、`FactorizableRate.lean:636`) を目標。固定-`U` framing は小さい `U` で false-as-framed だったが inf-over-all で source から解消 → sizing precondition (旧 hU_card) 不要。ただし **Carathéodory/compactness は左端点右連続 `wynerZivRate_le_of_forall_pos_add_endpoint` (`Converse.lean:1773`) の L1 crux として critical path 上** (cosmetic ではない、slug `wz-auxiliary-cardinality-bound`、P2)。非退化は `wzObjective_nonneg_of_factorizable` → `wzRateValueSet_bddBelow_of_pmf` が junk `sInf ∅ = 0` を防止 (confidence: human-judgment、reshape 独立 honesty-audit PASS 2026-07-05)。
- single-letterisation の真ルート = `Uᵢ=(J,Y_{\i})` + conditional-MI chain、真 gateway = `iIndepFun → Markov Uᵢ−Xᵢ−Yᵢ` (`wz_perletter_markov`)。Csiszár `csiszar_sum_identity_hetero` (`ConverseGateway.lean:48`) は distortion 側が one-sided aux を強制するため本ルート **orphaned** (削除せず維持、wall ではない、confidence: human-judgment、proof-pivot consult)。このルートで witness core (sub2/sub3/gateway) は leg 8 で CLOSED (再検証 `#print axioms`、prose にキャッシュしない)。
- 残 converse own-sorry = 左端点右連続 `wynerZivRate_le_of_forall_pos_add_endpoint` (`Converse.lean:1773`、`@residual(plan:wyner-ziv-main-plan)`、headline case C `Converse.lean:1934` からのみ consume)。proof-pivot-advisor: 大型 self-build (安価な単調極限は minimax 障害でブロック)、Carathéodory L1/L2/L3 route (confidence: human-judgment、proof-pivot consult 2026-07-05)。
- Mathlib に operational coding-theory / method-of-types / Csiszár は **完全不在** (loogle `Csiszar`/`rateDistortion`/`WynerZiv`/`typicalSet` = Found 0、confidence loogle-neg)。すべて in-project。→ 撤退 class は `plan` (wall ではない)。
- StandardBorel は `[Fintype][MeasurableSpace][MeasurableSingletonClass]` から `#synth` で自動 derive、明示追加は `[Nonempty]` のみ (confidence: machine、`csiszar_sum_identity_hetero` が variable block のみで 0 sorry を実証)。inventory §4/§6/§7 の反対記述 + item #6 は MOOT。

(これ以上のキャッシュはしない。`wyner-ziv-facts.md` は現時点で作らない。)

## 判断ログ

append-only。決着済 entry は削除 (git が履歴)、active のみ残す。≤ 10 entry。

1. **reshape 採択 (proposal A、commit `4532bd48`、active)**: converse を固定-`U` rate `wynerZivRateFactorizable U` から **全有限補助 alphabet 上 inf** `wynerZivRate` (`FactorizableRate.lean:636`、union-of-images `sInf`) に retarget。旧固定-`U` framing は小さい `U` で false-as-framed (sInf が `|U|` に antitone、Carathéodory 閾値 `|α|+1` 未満で inf が achievable `R` を真に超える) → 旧回避策の `hU_card` sizing 前提 + converse critical path 上 Carathéodory support を **両方撤去**。reshape で large single-letterisation auxiliary が `wynerZivRate_le_of_feasible` (`FactorizableRate.lean:678`) で直接 feasible 点に着地、Carathéodory は cosmetic equivalence に降格。非退化は `wzObjective_nonneg_of_factorizable` → `wzRateValueSet_bddBelow_of_pmf` が junk `sInf ∅ = 0` を防止。独立 honesty-auditor PASS (非退化・非 load-bearing・retarget は strictly stronger)。両 headline は `wynerZivRate` を目標に、converse は `∀`-clean。
2. **single-letterisation の真ルート (proof-pivot consult、旧「converse = pure plumbing」を覆す、番号凍結 = 親参照)**: distortion 側 (`X̂ᵢ = decoder(J,Yⁿ)ᵢ` が `Yⁿ` 全体依存) が one-sided aux `Uᵢ=(J,Y^{i-1})` を禁じ `Uᵢ=(J,Y_{\i})` を強制 → Csiszár `csiszar_sum_identity_hetero` は本ルート **orphaned** (削除せず維持、wall ではない)、rate step は conditional-MI chain (`∑[I(Xᵢ;Uᵢ)−I(Yᵢ;Uᵢ)] = ∑I(Xᵢ;Uᵢ|Yᵢ) = ∑I(Xᵢ;J|Yⁿ) ≤ I(Xⁿ;J|Yⁿ) = I(J;Xⁿ)−I(J;Yⁿ)`)。真 gateway = `iIndepFun → Markov Uᵢ−Xᵢ−Yᵢ` (`wz_perletter_markov`)。**このルートで witness core (sub2/sub3/gateway) を leg 8 で CLOSED** (`4eb1a788`/`95f4abc5`/`321abbc6`/`72a9077e`/`021d7732`、sorryAx-free + 独立監査 PASS)。
3. **StandardBorel 訂正を反映 (item #6 MOOT)**: `#synth` で StandardBorel が `[Fintype+MSC]` から自動 derive すると実測判明 (gateway probe)。inventory §4/§6/§7 の「自動導出されない → `attribute [local instance]` file 限定発火」は誤り、local-instance サブタスク不要、明示追加は `[Nonempty]` のみ。
4. **撤退 class = `plan` (wall ではない、active)**: WZ gap は Mathlib gap でなく in-project atom 合成の未実装 (inventory §8)。既定退避 = `@residual(plan:wyner-ziv-main-plan)`、split-out は `wz-binning-covering`/`wz-auxiliary-singleletter`。wall 昇格は side-info covering が真の Mathlib gap と gateway-atom-first で判明した場合のみ後続 PR で。
5. **親再開の注記 (active)**: 親 [`wyner-ziv-moonshot-plan.md`](wyner-ziv-moonshot-plan.md) は ACTIVE (情報側完成 record 保存)。textbook-roadmap Ch.15 の「WZ main scope-out」行は **closure まで維持** (attack ≠ scope 再開の確定、roadmap は本 planner の editing boundary 外)。
6. **次 leg 群の着手選択 (active)**: converse core CLOSED 後、Goal の残りは 2 チャンク — (a) converse 左端点右連続 endpoint (`wynerZivRate_le_of_forall_pos_add_endpoint`、L1 Carathéodory gateway-atom-first、~330-630 行) と (b) achievability P3 (binning+covering、未着手、~800-1500 行、Goal の残り半分)。次 leg はいずれかを選ぶ。endpoint は headline case C からのみ consume の transitive load-bearing で permanent scope-out 不可 → 優先度高だが L1 HIGH risk。

_(decision #4「distortion 述語形」は P1 で確定・削除: **distortion-only** `∀ε>0,∀ᶠ n, 歪≤D+ε` (= limsup≤D) を採用。誤り確率は predicate 外の achievability-internal 量に。`WynerZivAchievable` は `@audit:ok`。)_
