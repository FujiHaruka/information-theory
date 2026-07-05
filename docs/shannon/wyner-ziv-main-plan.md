# Wyner–Ziv operational main theorem (achievability + converse) サブ計画

> **Parent**: [`wyner-ziv-moonshot-plan.md`](wyner-ziv-moonshot-plan.md) §operational main relay

**Status**: ACTIVE 🚧 — feasibility CONFIRMED (converse gateway `csiszar_sum_identity_hetero` proved sorryAx-free, commit `b780f782`)。operational code ↔ R_WZ(D) を繋ぐ **achievability + converse** (Cover–Thomas Thm 15.9.1) を genuine closure する。情報側 R_WZ(D) は完成済 (`WynerZiv/` 5 file、0 sorry)。

**SoT / 在庫**: [`wyner-ziv-main-inventory.md`](wyner-ziv-main-inventory.md) (§2 提案 statement / §5 achievability 資産 / §6 converse 資産 / §7 self-build 7 項目 / §10 gateway atom)。

**再検証** (prose にキャッシュしない): `scripts/sig_view.ts --sorry InformationTheory/Shannon/WynerZiv/*.lean` / `#print axioms <headline>`。

## 進捗

- [x] M0 — API 在庫 (既存 [`wyner-ziv-main-inventory.md`](wyner-ziv-main-inventory.md) で代替) + converse gateway 実証 ✅ (`csiszar_sum_identity_hetero`、sorryAx-free、`ConverseGateway.lean:48`)
- [x] P1 — statement scaffolding ✅ **proof-done sorryAx-free** (`fdbae7f9`)。`WynerZivAchievable` (distortion-only、`@audit:ok`) + pmf↔measure MI 橋 2 本 (`wzMutualInfoXU/YU_eq_mutualInfo`、closed sorry-free)。`wzErrorProb` は predicate 外に (achievability-internal、P3 へ)。`Operational.lean` 全 0 sorry
- [~] P2 — converse **reshape 後、headline body closed + time-sharing 基盤完成、残 sorry 2 本** (leg 5、`481e0c37`)。両 headline (`wyner_ziv_converse` + 中間 `wyner_ziv_converse_n_letter_singleLetter`) は `wynerZivRate` に retarget 済。**leg 4-5 で以下を genuine closure (sorryAx-free + 独立監査 PASS)**: gateway `wzObjective_nonneg_of_factorizable` (DPI 非負)、`h_sl` landing、**time-sharing 基盤** `wzRateValueSet_timeShare_mem` + `wynerZivRate_convex_in_D` + `mutualInfoPmf_mixture_affine` (`afb33ce4`/`c5d147fa`、`FactorizableRate.lean §10`)、**headline `wyner_ziv_converse` body sorry-free** (`4bf50ba7`、i.i.d.-pi 源 + n-letter + ε→0 の case A/B genuine、time-sharing perturbation で interior 右連続閉)。`Converse.lean` の残 sorry は **2 本**、すべて `@residual(plan:wyner-ziv-main-plan)`: (1) **`wz_converse_feasible_point` (L519)** — single-letterization core (Csiszár exact identity + per-letter Markov `Uᵢ−Xᵢ−Yᵢ` + time-sharing 合成、**残の重心**、gateway atom 再利用可)、(2) **`wynerZivRate_le_of_forall_pos_add_endpoint` (L719)** — 左端点 `D=D_min` の右連続性 (`wz-auxiliary-cardinality-bound` = Carathéodory/compactness、下記)。🚧
- [ ] P3 — achievability body (binning + covering ハイブリッド、本計画の重心) 📋
- [ ] PV — verify (`#print axioms` sorryAx-free + 独立 honesty 監査 + root 配線) 📋
- [ ] `wz-auxiliary-cardinality-bound` (Carathéodory/compactness) — **leg 5 で critical path に再浮上**。当初は cosmetic equivalence `wynerZivRate = wynerZivRateFactorizable (Fin (|α|+1))` として critical path 外に降格していたが、headline の ε→0 段で **左端点 `D=D_min` の右連続性** (`wynerZivRate_le_of_forall_pos_add_endpoint` L719) が bounded-auxiliary compactness を要求するため、この論法が endpoint residual 経由で critical path に戻った。中身 = 近最適 feasible kernel 列の収束部分列抽出 (有限 alphabet MI 連続 + Carathéodory 有界補助) → 極限が D-feasible で objective = lim R(D+ε) → antitone と合わせ右連続。interior (`∃ D₀<D` feasible) は time-sharing perturbation で既に閉、**残るは左端点のみ**

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

WZ operational main = **RD covering (lossy 側) と SW binning (side-info 側) の 2 段ハイブリッド**。両家系の atom は inventory §5/§6 で「reusable as-is」がほぼ全部と確定済 (Mathlib gap ゼロ、すべて in-project)。gap は 2 箇所に局在: (i) **converse の auxiliary `Uᵢ:=(J,Y^{i-1})` 同定橋** (§7 #3)、(ii) **achievability の binning+covering 接着** (§7 #2)。攻略は **converse-first の confidence-builder** 順:

1. **converse を先に閉じる (pure plumbing 公算大)**。決定的 gateway = heterogeneous Csiszár `csiszar_sum_identity_hetero` は **既に sorryAx-free で proved** (同型版証明を verbatim port、chain-rule stack が polymorphic だったため)。骨格 `rate_distortion_converse_n_letter_singleLetter` (`ConverseNLetter.lean:659`、antitone+Jensen+superadd+DPI 連鎖) を流用。auxiliary `Uᵢ:=(J,Y^{i-1})` の cross 項相殺は **exact Csiszár sum identity** (`csiszar_sum_identity_hetero`) で行う — broadcast-channel の `bc_input_singleletterize` (channel single-letterization、premise が別) は **テンプレとして使わない** (WZ は channel single-letterization ではなく exact identity)。凸性・単調性 (`wynerZivRateFactorizable_convex_in_D` / `_antitone`) は情報側完成品を直呼び。reshape 後は large auxiliary が `wynerZivRate_le_of_feasible` で直接 feasible 点に着地するため Carathéodory sizing は不要。残る real gap = single-letterization core (`h_sl`) + data-processing 非負 (`wzObjective_nonneg_of_factorizable`、gateway atom)。**MAC converse の教訓 (gateway 通過後は骨格クローンで genuine closure) が WZ にも効く公算大**。

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
| converse gateway | `csiszar_sum_identity_hetero` (`ConverseGateway.lean:48`、**sorryAx-free**) | cross 項相殺。**既に proved** |
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

## P2 — converse body (single-letterization、reshape 後 3-sorry)

**ファイル**: `InformationTheory/Shannon/WynerZiv/Converse.lean` (`ConverseGateway` + `FactorizableRate` §10 + `Operational` に依存)
**proof-log**: yes (single-letterization は converse の実体、再開根拠に必須)

reshape (`4532bd48`) で両 headline を `wynerZivRate` に retarget 済、`hU_card` / Carathéodory は critical path 外。残 sorry は 3 本 (すべて `@residual(plan:wyner-ziv-main-plan)`、再検証 `scripts/sig_view.ts --sorry InformationTheory/Shannon/WynerZiv/Converse.lean`):

- [ ] **(sorry 1) `wzObjective_nonneg_of_factorizable`**: data-processing 非負 `0 ≤ wzMutualInfoXU − wzMutualInfoYU`。gateway atom (`wynerZivRate` の非退化 = `wzRateValueSet_bddBelow_of_pmf` の入力)。measure 形 DPI `mutualInfo_le_of_markov` + pmf↔measure 橋で **in-project buildable (Mathlib 壁ではない)**。
- [ ] **(sorry 2) `h_sl`** (in `wyner_ziv_converse_n_letter_singleLetter`): single-letterization core。chain rule で auxiliary `Uᵢ:=(J,Y^{i-1})` を identify → cross 項を exact `csiszar_sum_identity_hetero` (proved) で相殺 → per-letter を `wynerZivRate_le_of_feasible` (`FactorizableRate.lean:678`) で feasible 点に着地 → n-ary Jensen + pmf↔measure 橋。**残の重心**。
- [ ] **(sorry 3) headline `wyner_ziv_converse`**: `WynerZivAchievable → wynerZivRate ≤ R`。中間 `wyner_ziv_converse_n_letter_singleLetter` を asymptotic に詰める。
- [x] **sorry-free 済**: step 6 block bound `mutualInfo_diff_le_log_card` (`Converse.lean:89`、private) + `(1/n)`-scaling + `wzRateValueSet_bddBelow_of_pmf` (non-degeneracy、`wzObjective_nonneg_of_factorizable` を transitive 継承)。

- **依存 in-project decl**: `ConverseNLetter.lean:659` (骨格)、`:422` (`condEntropy_pi_le_sum_condEntropy_per_letter`)、`:532` (`mutualInfo_superadditive_of_indep`); `WynerZiv/ConverseGateway.lean:48` (hetero Csiszár); `FactorizableRate.lean:636/678` (`wynerZivRate` / `wynerZivRate_le_of_feasible`)、`FactorizableRate.lean` (`_convex_in_D` / `_antitone`); `ConditionalEntropyConvexity.lean:374` (`_unconditional`); measure 形 DPI `mutualInfo_le_of_markov`。**`bc_input_singleletterize` は不採用** (broadcast channel single-letterization、premise が別)。
- **gateway atom**: heterogeneous Csiszár = **既に proved sorryAx-free**。残 = `h_sl` (single-letterization core) + `wzObjective_nonneg_of_factorizable` (DPI 非負)。
- **撤退条件 (honest、hypothesis bundling 禁止)**: 各 sorry は既に `@residual(plan:wyner-ziv-main-plan)` で type-check done 着地済 (本計画内 closure)。single-letterization core が単独で重く独自 closure plan を要すると判明した場合のみ split-out plan へ **`@residual(plan:wz-auxiliary-singleletter)`** (kebab-case、新 plan filename stem) にエスカレート。auxiliary `Uᵢ:=(J,Y^{i-1})` の同定を `*Hypothesis`/`*Reduction` predicate に **bundle しない** (tier-5 禁止)。regularity hyp (`IsProbabilityMeasure` / 可測性 / `iIndepFun` / memoryless-Markov / `Nonempty`) は precondition で OK。

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

**deferred (別 plan、cosmetic、critical path 外)**: `wynerZivRate = wynerZivRateFactorizable (Fin (|α|+1))` の Carathéodory equivalence (§7 #7) → slug `wz-auxiliary-cardinality-bound`。reshape 後 main converse は `wynerZivRate` (全有限補助 alphabet 上 inf) を直接目標にするためこの equivalence を **要しない** = critical path 外、file は現時点で不要。本計画にサブタスクは置かない。

## settled-facts (minimal、再導出可能なものは都度 `#print axioms` / `rg`)

- reshape (`4532bd48`): operational headline は `wynerZivRate` (全有限補助 alphabet `Fin k` 上 `sInf`、`FactorizableRate.lean:636`) を目標。固定-`U` framing (`wynerZivRateFactorizable U`) は小さい `U` で false-as-framed だったが inf-over-all で source から解消 → **sizing precondition (旧 hU_card) 不要、Carathéodory は critical path 外** (cosmetic equivalence に降格)。非退化は `wzObjective_nonneg_of_factorizable` → `wzRateValueSet_bddBelow_of_pmf` が junk `sInf ∅ = 0` を防止 (confidence: human-judgment、reshape 独立 honesty-audit PASS 2026-07-05)。
- converse gateway `csiszar_sum_identity_hetero` (`ConverseGateway.lean:48`) sorryAx-free (confidence: machine、再検証 `#print axioms InformationTheory.Shannon.WynerZiv.csiszar_sum_identity_hetero`)。同型版証明の verbatim port が通った = chain-rule stack が polymorphic だった。
- Mathlib に operational coding-theory / method-of-types / Csiszár は **完全不在** (loogle `Csiszar`/`rateDistortion`/`WynerZiv`/`typicalSet` = Found 0、confidence loogle-neg)。すべて in-project。→ 撤退 class は `plan` (wall ではない)。
- StandardBorel は `[Fintype][MeasurableSpace][MeasurableSingletonClass]` から `#synth` で自動 derive、明示追加は `[Nonempty]` のみ (confidence: machine、`csiszar_sum_identity_hetero` が variable block のみで 0 sorry を実証)。inventory §4/§6/§7 の反対記述 + item #6 は MOOT。

(これ以上のキャッシュはしない。`wyner-ziv-facts.md` は現時点で作らない。)

## 判断ログ

append-only。決着済 entry は削除 (git が履歴)、active のみ残す。≤ 10 entry。

1. **reshape 採択 (proposal A、commit `4532bd48`、active)**: converse を固定-`U` rate `wynerZivRateFactorizable U` から **全有限補助 alphabet 上 inf** `wynerZivRate` (`FactorizableRate.lean:636`、union-of-images `sInf`) に retarget。旧固定-`U` framing は小さい `U` で false-as-framed (sInf が `|U|` に antitone、Carathéodory 閾値 `|α|+1` 未満で inf が achievable `R` を真に超える) → 旧回避策の `hU_card` sizing 前提 + converse critical path 上 Carathéodory support を **両方撤去**。reshape で large single-letterisation auxiliary が `wynerZivRate_le_of_feasible` (`FactorizableRate.lean:678`) で直接 feasible 点に着地、Carathéodory は cosmetic equivalence に降格。非退化は `wzObjective_nonneg_of_factorizable` → `wzRateValueSet_bddBelow_of_pmf` が junk `sInf ∅ = 0` を防止。独立 honesty-auditor PASS (非退化・非 load-bearing・retarget は strictly stronger)。両 headline は `wynerZivRate` を目標に、converse は `∀`-clean。
2. **攻略順序 = converse-first (confidence-builder)**: converse は decisive gateway (hetero Csiszár) が既に sorryAx-free で proved = pure plumbing 公算大ゆえ先に閉じ、achievability (重心、gateway 未試行) を後に回す。P1 scaffolding は両 leg の前提ゆえ最初。
3. **StandardBorel 訂正を反映 (item #6 MOOT)**: `#synth` で StandardBorel が `[Fintype+MSC]` から自動 derive すると実測判明 (gateway probe)。inventory §4/§6/§7 の「自動導出されない → `attribute [local instance]` file 限定発火」は誤り、local-instance サブタスク不要、明示追加は `[Nonempty]` のみ。
4. **撤退 class = `plan` (wall ではない、active)**: WZ gap は Mathlib gap でなく in-project atom 合成の未実装 (inventory §8)。既定退避 = `@residual(plan:wyner-ziv-main-plan)`、split-out は `wz-binning-covering`/`wz-auxiliary-singleletter`。wall 昇格は side-info covering が真の Mathlib gap と gateway-atom-first で判明した場合のみ後続 PR で。
5. **親再開の注記 (要 orchestrator アクション、active)**: 本サブ計画の起票に伴い親 [`wyner-ziv-moonshot-plan.md`](wyner-ziv-moonshot-plan.md) を CLOSED→ACTIVE に flip 済 (情報側完成 record は保存)。ただし textbook-roadmap Ch.15 の「WZ main scope-out」行は **closure まで維持** (attack ≠ scope 再開の確定、roadmap は本 planner の editing boundary 外)。

_(decision #4「distortion 述語形」は P1 で確定・削除: **distortion-only** `∀ε>0,∀ᶠ n, 歪≤D+ε` (= limsup≤D) を採用。誤り確率は predicate 外の achievability-internal 量に。`WynerZivAchievable` は `@audit:ok`。)_
