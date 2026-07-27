# Shannon: 一般 BC 容量領域フレーム サブ計画

> **Parent**: [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md) §L-BC5 後続

未解決問題「一般 2 受信者 BC の容量領域の特徴づけ」に対して形式化が提供できるのは **足場**
(内界 / 外界 / 両者による挟み込み) までで、未解決本体 (内外一致) は数学が存在しないので Phase 外。
本計画はその足場を組む。到達目標は `内界 ⊆ bcCapacityRegion ⊆ 外界` を Lean の 1 本の定理列として
持ち、一致が既知のクラスでは等号まで閉じること。確定事実の台帳は
[`bc-facts.md`](bc-facts.md) (再導出が高価なものだけ。機械で安いものは毎回引き直す)。

## 進捗

- [x] Phase 1 操作的容量領域 (主語) ✅ `fd39ad95` `deb930a7`
- [ ] Phase 2 補助変数 union 🔄 — 最小完遂 P1–P3 ✅ `fcdafaf5` `b1837901` / 拡張 P4–P7 📋。
      **等号の前提ではなくなった** (経路変更、判断ログ 18)
- [x] Phase 3 協調外界 (安い外界) ✅ `e9222d0a` `b9ba272a`
- [x] Phase 4a UV 単一文字化 (floating 形) ✅ `5bf64adf`…`54705cb3`
- [x] Phase 4b UV 外界の集合化 + 操作的包含 ✅ `6ddb1a48` `bfdd55e1` `c768cc00` (**全平面版**)
- [ ] Phase 5 一致クラスの拡張 🚧 ★現在の本線
  - [x] 定義段 (符号規約の対称化 + 3 クラス + 包含鎖) ✅ `2c938fe0`…`42ac21e7`
  - [x] 内外を同じ添字に載せる橋 S1–S6 ✅ `6b0c1ea1` `76b83bc1` `0186b708` `28eae4ea`
  - [ ] less noisy の等号 🔄 **経路変更** — 内界は Marton union ではなく **superposition**。
        S0–S4 ✅ `06817339`…`28aafa87` / S5 ✅ `c3508204`…`47933abd` /
        S6 ✅ `70fc424e`…`dd981e01` / S7 ✅ `560c3399` `069c6016` / **S8 📋 ★次の一手**

## 在庫

| 資産 | 場所 | 用途 |
|---|---|---|
| `BCAchievable` / `bcCapacityRegion` | `BroadcastChannel/Operational.lean:53` / `:68` | 主語。包含の左辺 |
| `bc_capacityRegion_isClosed` / `bc_achievable_mono` / `bc_mem_closure_of_strictly_below` | `Operational.lean:102` / `:71` / `:86` | 閉性・down-set 性・厳密不等号からの closure 回収 (3 本目が内界包含の主役) |
| `martonRegion` / `bc_strict_interior_achievable` / `marton_region_subset_capacity` | `Operational.lean` (168 行 / 8 decl) | Marton 内界の集合版と包含 (`@[entry_point]`)。**符号制約なしの全平面版** (`2c938fe0`) |
| **比較クラス 3 本 + 包含鎖** | `BroadcastChannel/Classes.lean` (253 行 / 9 decl) | `IsBCLessNoisy:63` / `IsBCMoreCapable:75` / `IsBCSemiDeterministic:83` と `@[entry_point]` 4 本 `bc_lessNoisy_infoJoint_ge:95` / `IsBCDegraded.isBCLessNoisy:133` / `IsBCLessNoisy.isBCMoreCapable:218` / `IsBCSemiDeterministic.exists_prob_real_singleton_eq_zero:236`。語彙橋 2 本 `bcJointDistribution_id_eq:166` / `mutualInfoOfChannel_map_eq_mutualInfo_bcJointDistribution:184`。**`IsBCLessNoisy` は `∀ (U : Type u) [Fintype U]` を量化する** ⟹ 達成側に渡す補助は有限型でなければならない (S5 の量子化の理由) |
| `bcOuterRegionCoop` / `bc_capacity_subset_coop` | `OuterBound.lean:380` / `:408` | 協調外界と包含 (`@[entry_point]`)。挟み込みの右辺その 1 |
| `BroadcastCode.restrict₁/₂` / `coop` + 誤り確率補題 | `OuterBound.lean:50`–`:262` | BC 符号 → 単一ユーザー符号への 3 通りの還元 |
| `channelCoding_operational_rate_le_capacity` | `ChannelCoding/StrongConverseAsymptotic.lean:805` | 操作的レート ≤ 容量 (`@[entry_point]`)。Phase 3 の心臓 |
| `uvAux` / 単一文字化 4 本 / `InBCOuterRegionUV` / `bc_uv_converse` | `OuterBoundUV.lean:71` / `:113` `:174` `:684` `:637` / `:735` / `:815` | Phase 4a。`uvAux` の**型が letter `i` に依存する**のが S5 の型統一の理由。headline は degradedness 前提なし (`@[entry_point]`) |
| **符号→ambient の共有層** | `ChannelCoding/CodeToAmbient.lean` (567 行 / 16 decl、MAC/BC 共有) | `isMarkovChain_of_compProd_pi:210` / `isMemorylessChannel_of_compProd_pi:322` / `le_log_of_ceil_exp_le:546` + BC 由来の汎用 3 本 (`compProd_comap_map_prodMap:346` / `compProd_pi_map_pair_eq_of_update_invariant:396` / `le_toReal_of_inv_mul_le:556`) + `isMarkovChain_map_comp:496` (F-a で上流移動) |
| **BC の符号→ambient 橋 + UV per-letter 情報スロット** | `BroadcastChannel/OuterBoundUV/Bridge.lean` (936 行 / 58 decl) | `bcConverseAmbient:141` → 構造前提 4 本 `:301`–`:428` → `bcConverseFanoSlack₁/₂:532`/`:541` → `bc_uv_converse_from_code:562` / `bc_uv_rate_extract:602` → `uvAuxPad:663` + 不変性 `:713`–`:738`。`section PerLetterInfo` (`:764`–`:934`) が 4 スロット `uvInfo₁:777` / `uvInfo₂:782` / `uvInfoSum₂:787` / `uvInfoSum₁:792` + `bcUVTuple:809` / `bcUVJointDistribution:833` + 同定 4 本 |
| **UV 外界の集合版** | `OuterBoundUV/Region.lean` (602 行 / 38 decl) + `OuterBoundUV/Assembly.lean:72` | チャネル整合条件 `IsUVChannelLaw:110` + 特徴づけ `isUVChannelLaw_iff:131` + 閉包性 5 本 + `.map_auxiliaries:183` / `.swap_auxiliaries:209` / `.map_input_output:234`。領域 `uvRegion:361` / `bcOuterRegionUV:373` / `_isLowerSet:393` / `_isClosed` / `_nonempty`。非退化の証拠 2 本。符号側の支払い `bcUVJointDistribution_isUVChannelLaw` だけ `Assembly.lean:72` |
| **S4 = 四つ組法 + Markov 鎖 3 本** | `OuterBoundUV/Region.lean` `### The Markov chains carried by a channel law` | `IsUVChannelLaw.map_auxiliary_input_output:251` (四つ組法、仮説は `[IsMarkovKernel W]` + `[SFinite ν]` のみ) / 親玉 `.isMarkovChain_UV_X_Y:287` (結論は **出力対のまま** `(U,V) → X → (Y₁,Y₂)`) / `.isMarkovChain_U_X_Y₁:305` / `.isMarkovChain_V_X_Y₁:325`。**Markov 鎖 3 本の `section Transport` は `[StandardBorelSpace _] [Nonempty _]` を 5 型すべてに + `[IsProbabilityMeasure ν]` を要求する** (四つ組法は要求しない) |
| **S5 = 補助の有限量子化** | `OuterBoundUV/Quantization.lean` (382 行 / 21 decl) | `uvQuantize:187` (`ℕ → ULift.{u} (Fin (m+1))`、切詰め) / `uvQuantizeLaw:196` (`ν.map (uvRelabel (uvQuantize m) id)`) / `uvQuantizeSlack:202` (`= ν {q \| m ≤ q.1} * ENNReal.ofReal (Real.log (Fintype.card β₂))`) / `_isUVChannelLaw:212`。**S6/S8 が消費する 3 本** = `uvInfo₂_le_uvQuantizeLaw_add_slack:341` / `uvInfoSum₂_le_uvQuantizeLaw_add_slack:347` / `tendsto_uvQuantizeSlack:363`。加えて任意の可測 `f : U → U'` に一般化された `IsUVChannelLaw.condMutualInfo_le_map_cond:126` (S6 の `Bool × U_m` でも当たる見込み) と汎用 3 本 `mutualInfo_ne_top_of_fintype_right:59` / `mutualInfo_le_ofReal_log_card:66` / `mutualInfo_eq_zero_of_ae_const:81` (置き場は §後続作業 F-15) |
| **時間共有 + 平均化 + 極限 + headline** | `OuterBoundUV/Assembly.lean` (851 行 / 35 decl) | 混合法 `bcUVTimeShare:258` (+ `_isUVChannelLaw:284` / `_eq_sum:272`) と 4 スロット平均化 `bcUVTimeShare_uvInfo₁_ge:315` 系。再ラベル一族 `uvRelabel:134`–`:211` (S5 / S6 / S7 が全部使う。`uvInfoSum₂_map_uvRelabel` は `[Fintype U]` を要求)。縮小点の**乗法形** `bc_uv_code_point_mem:609` → `bc_uv_rate_point_mem:635` → `bc_uv_shifted_point_mem:696` → `bc_uv_quadrant_mem_of_achievable:784` → headline `bc_capacity_subset_uv:839` (`@[entry_point]`) |
| 汎用資産 (BC 非依存、自作) | `CodeToAmbient.lean` の 3 本 / `Shannon/CondMutualInfoMixture.lean` (193 行 / 7 decl) | 再符号化不変 3 本 `mutualInfo_eq_of_leftInverse:40` / `mutualInfo_congr_ae:57` / `condMutualInfo_eq_of_leftInverse_cond:66` + 混合法 3 本 `condMutualInfo_compProd_fst_eq_lintegral:102` / `mutualInfo_compProd_eq_add_lintegral:142` / `condMutualInfo_compProd_snd_eq_lintegral:164` (**S6 の核**)。混合法は**絶対連続性の仮説を持たない等式** |
| `csiszar_sum_identity_cond` / `csiszar_sum_identity` | `OuterBoundUV/Gateway.lean:246` / `BroadcastChannel/ConverseGateway.lean:142` | 条件付き Csiszár 和恒等式 (Phase 4a の核) と無条件版 |
| `bc_converse` / `bc_input_singleletterize` | `BroadcastChannel/Converse.lean:571` / `:316` | degraded 限定の converse (floating 形)。**degradedness を `h_deg_block` で受ける**ので 4b の橋はそのままでは効かない (判断ログ 11-(n)) |
| **達成側の共通形 3 本 + degraded headline** | `BroadcastChannel/Achievability/Assembly.lean` | `bc_ceil_exp_max_zero:1080` / `bc_Ec_lt_of_clamped_rate:1090` / **`bc_achievability_of_rate_lt:1103`** (レートの符号制約なし、`hJlt : max R₁ 0 + R₂ < bcInfoJoint`) / `bc_achievability_of_infoJoint_ge:1239` (`hsum` 形) / `bc_achievability:1270` (**署名・結論は逐語不変**) / `bc_degraded_infoJoint_ge:967` |
| **superposition 内界 (S0–S2)** | `BroadcastChannel/SuperpositionRegion.lean` (209 行 / 7 decl、import 3 本) | `bcInfo₁_nonneg:50` / `@[entry_point]` `bc_lessNoisy_achievability:143` / def `bcSuperpositionRegionFullSupport:178` / `@[entry_point]` `bcSuperpositionRegionFullSupport_subset_capacity:189` (仮説は `hW` + `hln` のみ)。**less noisy の言葉で挟み込みが並ぶ** |
| **S3 = 情報量スロットの同定 3 本** | 同上 `### The three informations as (conditional) mutual informations` | `bcInfo₂_eq_mutualInfo_toReal:78` (`= I(U;Y₂).toReal`) / `bcInfoJoint_eq_mutualInfo_toReal:90` (`= I((U,X);Y₁).toReal`) / `bcInfo₁_eq_condMutualInfo_toReal:110` (`= I(X;Y₁∣U).toReal`)。`U` は `Type*` 総称 ⟹ **more capable でも再利用可**。型クラス前提は逐語 `[Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]` + `[IsProbabilityMeasure pU]` / `[IsMarkovKernel K]` / `[IsMarkovKernel W]` |
| **S6 = 時分割の補助への吸収** | `BroadcastChannel/SuperpositionTimeShare.lean` (545 行 / 32 decl、import 2 本) | 到達点 `exists_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw:471` — 外界の 3 不等式 (`h₁` / `h₂` / `hsum`) を満たす点から達成側の対 `(pU, K)` を**実際に構成して**返す。仮説は `[IsMarkovKernel W]` / `hln : IsBCLessNoisy W` / `h : IsUVChannelLaw W ν` / 3 不等式のみ。補助 `exists_bcInfo_ge_of_tagged:446` が「再ラベル + 対の取り出し」を分離。混合側 `uvTimeShareLaw:114` (+ `_eq:123` / `_isUVChannelLaw:158`) と `uvBranchKernel_ae_tag:131` は **`lam ≤ 1` を要求しない** (`⊓ 1` clamp で無条件)。cloud 側 `uvCloudLaw:309` / `uvSatelliteKernel:314` + スロット同定 3 本 `bcInfo₂_uvCloudLaw:359` / `bcInfo₁_uvCloudLaw:366` / `bcInfoJoint_uvCloudLaw:375`。汎用の自作 `boolLaw:58` 一族 3 本 + `condMutualInfo_eq_mutualInfo_of_ae_const:186` (置き場は §後続作業 F-15) |
| **S7 = 全支持への摂動** | `BroadcastChannel/SuperpositionFullSupport.lean` (802 行 / 44 decl、import 2 本) | 到達点 `@[entry_point]` 2 本 = 対レベルの `exists_fullSupport_bcInfo_ge:720` (対 `(pU, K)` を**全支持の対**に slack `δ` 以内で置き換える) と S6 と合成済の `exists_fullSupport_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw:768`、加えて内界 union への着地版 `sub_mem_bcSuperpositionRegionFullSupport_of_lessNoisy_of_isUVChannelLaw:786`。摂動は五つ組の世界: `uvUniformLaw:174` / `uvPerturbLaw:190` (+ `_isUVChannelLaw:205` / `_map_aux_input_pos:237`) と 2 スロットの損失評価 `mul_condMutualInfo_le_condMutualInfo_uvPerturbLaw:567` / `mul_uvInfo₂_sub_binEntropy_le_uvInfo₂_uvPerturbLaw:592` (**後者の加法ペナルティは `Real.binEntropy`**、判断ログ 22)。一般混合 `uvMixLaw:306` 一族 (S6 の分岐クラスタの一般形) / 対 → 五つ組の糊 `uvLawOfInput:68` + `uvLawOfPair:705`。汎用の自作 4 本は §後続作業 F-15 |
| **内界の Marton union** | `BroadcastChannel/MartonUnion.lean` (110 行 / 5 decl) | `bcAuxAlphabet:52` (`= ULift.{u} (Fin (k+1))`) / `martonRegionUnion:58` / `martonRegionUnionFS:68` + `@[entry_point]` 2 本 `martonRegionUnion_subset_uv:81` (明示仮説ゼロ) / `martonRegionUnionFS_subset_capacity:101` + `_subset_union:88`。**superposition 路の補助アルファベットとしても再利用中** — `uvQuantizeLaw ν m` の第 1 成分は `ULift.{u} (Fin (m+1))` = `bcAuxAlphabet m` と**同じ型**なので、S8 で内界の union 添字に載せる橋は無料 |
| `marton_achievability` / `InMartonRegion` | `Marton/Achievability.lean:767` / `Marton/Basic.lean:40` | 一般 BC 内界 (EGK Thm 8.3、private message のみ、**共通補助 `U₀` なし**) と 3 不等式バンドル |
| **内外の橋 (S1–S6、全段 proof done)** | `OuterBoundUV/MartonBridge.lean` (525 行 / 31 decl) + `Region.lean:209` | `martonJointDistribution_isUVChannelLaw:70` → `martonSwapLaw:117` → `martonUVLaw:160` + `_isUVChannelLaw:177` + 4 スロット保存 `uvInfo₁_martonUVLaw:186` 系 / `.toReal` 同定 3 本 `:228` `:240` `:252` / 和レート 4 本 `:419` `:441` `:465` `:481` (核は Markov 鎖 2 本 `:275` `:301` + 条件付き DPI) / `marton_region_subset_uv:502` (`@[entry_point]`) |
| 情報量の道具 | `Shannon/CondMutualInfo.lean:214` / `:356` / `ChannelCoding/ConverseMemorylessChainRule.lean:113` `:164` / `OuterBoundUV/Gateway.lean:194` | 連鎖律 `mutualInfo_chain_rule` / DPI `mutualInfo_le_of_markov` / 条件付き DPI `condMutualInfo_le_of_markov_joint` / 条件付き連鎖律 `condMutualInfo_chain_rule_X_2var` (S5 が実際に使った) / `condMutualInfo_le_add_condMutualInfo` |
| エントロピー / MI ↔ エントロピー形 | `MaxEntropy/Basic.lean:229` / `MultipleAccess/Reconciliation.lean:45` / `Shannon/Entropy.lean:200` / `:42` / **`Shannon/Pi.lean:36`** | `entropy_le_log_card` / `mutualInfo_toReal_eq_entropy_form` / `condMutualInfo_eq_condEntropy_sub_condEntropy` / `entropy_pair_eq_entropy_add_condEntropy` / **`entropy_measurableEquiv_comp`** (平坦↔入れ子の再ラベル、判断ログ 16) |
| MAC の先例 | `MultipleAccess/TimeSharing.lean:49`–`:66` / `TimeSharingConverse/Bridge.lean` / `Assembly.lean` / `Reconciliation.lean:292` | 操作的述語 → closure で集合化 / 符号→ambient 橋の雛形 / 内外を同じ言語に揃える先例。**退化被覆と平均化は雛形にならない** (判断ログ 11-(f)) |

**存在しないもの** (等号が要求し、まだ書かれていないもの): (a) 逆包含
`bcOuterRegionUV W ⊆ bcSuperpositionRegionFullSupport W` (**等号に残る唯一の包含**)。量子化 + 裾評価
は S5、時分割の補助への吸収は S6、全支持への摂動は S7 で入り、残りは **組み立て (S8) だけ**。
(b) more capable の 3 制約を受ける structure (`InBCCapacityRegion` は 2 field)、(d) `IsBCDegraded W`
から `bcConverseAmbient` 上の per-letter Markov 鎖 `h_deg_block` を出す補題、(e)
`(mutualInfo μ Xs Xs).toReal = entropy μ Xs` と決定的写像の条件付きエントロピー消失
(semi-deterministic 用)。**Mathlib 側の穴はゼロ** (S7 在庫まで 7 leg 連続で 0 件)。旧 (a)
「`bcOuterRegionUV ⊆ martonRegionUnionFS`」は**偽** (判断ログ 18、[`bc-facts.md`](bc-facts.md))。

## ゴール / Approach

**「まず外界」は半分正しい。その前に主語が要る。**

Approach は **「主語 → 安い外界で挟み込みの骨格 → 本命の外界 → 一致クラスの拡張」** の 4 段。
外界の重い仕事の前に Phase 1 で `bcCapacityRegion W : Set (ℝ × ℝ)` を定義し、Phase 3 の緩い外界で
**一度挟み込みを完成させてしまう**。以後の外界の改良はすべて「同じ挟み込みの右辺を狭める」差分
作業になり、1 本ごとに独立して価値が出る。逆順 (先に UV outer bound を作る) だと、最も重い Phase
が最初に来るうえ、完成しても内界と並べられない。この順序は Phase 1/3/4b の実績で正当化された。

**Phase 4 を 4a / 4b に割る**、というのが外界側の主判断。情報量レベル (4a、難所は Csiszár 和恒等式
の適用形、ambient を与えられたものとして受ける floating 形) と操作的レベル (4b、難所は符号から
ambient を構成する橋と n 文字平均の単一文字化) で難所が別物だから。Phase 3 がこの分割を要求しなかった
のは Wolfowitz strong converse の対偶で **ambient の構成を丸ごと迂回できた**から。

**内界側は「1 本」ではなく「クラスごとに選ぶ」** (経路変更後の主判断、判断ログ 18)。in-project の
内界は Marton union (一般 BC 向け・共通補助 `U₀` なし) と superposition (cloud + satellite) の 2 本
で、**前者は劣化 BSC 対ですら容量領域より真に小さい**ので等号を狙うクラスでは後者を使う。Marton
union の順包含 `martonRegionUnion ⊆ bcOuterRegionUV` は一般 BC の内界としてそのまま残る。

## Phase 詳細

### Phase 1 / 3 / 4a ✅ (完了、1 行圧縮)

- **Phase 1** 主語を作る `fd39ad95` `deb930a7` — `BCAchievable` / `bcCapacityRegion := closure {…}` /
  `martonRegion` + `marton_region_subset_capacity`。proof-log: no
- **Phase 3** 協調外界 `e9222d0a` `b9ba272a` — BC 符号を 3 通りに還元して `bcOuterRegionCoop` +
  `bc_capacity_subset_coop`。**これで (緩い外界ながら) 挟み込みが完成**。proof-log: no
- **Phase 4a** UV 単一文字化 `5bf64adf`…`54705cb3` — 補助変数を `uvAux` 1 本に統一し identification が
  2 通りの instantiation に縮んだ。核は新規自作 `csiszar_sum_identity_cond`。proof-log: no

### Phase 2 — 補助変数についての union 🔄

M0 在庫は [`bc-phase2-union-inventory.md`](bc-phase2-union-inventory.md) (Mathlib の壁 0 件)。
最小完遂 P1–P3 ✅ (`ce8e9d0b` 在庫 / `fcdafaf5` 実装 / `b1837901` style) で
`BroadcastChannel/MartonUnion.lean` を新設し、補助の型 `k₁ k₂` と分布 `pV` / `K` についての union を
`closure` で取った (定義そのものは §在庫 の行番号が SoT)。設計の 3 点はいずれも**機械確認済**なので
蒸し返さないこと: (a) `Fin (k+1)` であって `Fin k` でない (`k = 0` で `Nonempty` が出ない)。
(b) `ULift.{u}` が要る (`IsBCLessNoisy` が `∀ (U : Type u)` を量化)。(c) `closure` を外側に取る
(比較先が閉集合なので包含に損がない)。**配置はトップ直下** (`Marton/` へ移すと `OuterBoundUV/` との
依存が双方向 = `module-structure.md` §5 違反)。

⚠ **正直な限界 (実際に発火した)**: この `martonRegionUnion` は共通補助 `U₀` を持たない Marton 内界で、
**劣化 BSC 対で `martonRegionUnionFS ⊊ bcCapacityRegion`** として限界が現れた (判断ログ 18)。

**拡張 P4–P7 📋 — いずれも等号の前提ではない** (行数見積りは在庫 §12 が SoT)。API の完全性と L-BCO2 の完答:

- [ ] **P4** 非空性 / 下方集合性 (~30 行、`Region.lean` の外界版が雛形)
- [ ] **P5** `Convex ℝ (martonRegion pV K W)` (~20 行、任意)。probe 実測済
- [ ] **P6** 補助アルファベットの付け替え不変性 (~110 行)。**これが閉じたら L-BCO2 は「答えた」になる**
- [ ] **P7** 全支持の除去 (~180 行)。**superposition 側の対応物 S7 は実測 802 行**だったので、この
      見積りは probe を取るまで信じないこと (判断ログ 23)

**時分割 / 凸包は要らない** (在庫 §6 が実測で決着): 各 `martonRegion` は凸、union は非凸だが相手側
`bcOuterRegionUV` も非凸なので両辺が並ぶ。時分割変数 `Q` の補助への吸収は Marton では効かない
(`I(V₁;V₂)` が `H(Q)` だけ増える) が、**superposition の 2 制約領域では効いた** (S6 ✅)。
proof-log: no。

### Phase 4b — UV 外界の集合化 + 操作的包含 ✅ CLOSED

`6ddb1a48` / `bfdd55e1` `c768cc00`。headline
`bc_capacity_subset_uv : bcCapacityRegion W ⊆ bcOuterRegionUV W` (`@[entry_point]`) を**全平面版**で
達成 — 明示仮説は `W` と `[IsMarkovKernel W]` のみ。M0 在庫は
[`bc-uv-operational-inventory.md`](bc-uv-operational-inventory.md)。**L-BCO4 / L-BCO5 / L-BCO6 いずれも不発動**。

**領域定義の確定形 (Phase 5 が参照する SoT)**:

```
bcOuterRegionUV W = closure (⋃ (ν : ProbabilityMeasure (ℕ × ℕ × α × β₁ × β₂))
                               (_ : IsUVChannelLaw W ↑ν), uvRegion ↑ν)
uvRegion ν = {p | InBCOuterRegionUV p.1 p.2 (uvInfo₁ ν).toReal (uvInfo₂ ν).toReal
                    (uvInfoSum₂ ν).toReal (uvInfoSum₁ ν).toReal}
```

closure は不可避 (半平面の交差の union は閉じない) だが、それが `bcOuterRegionUV_isClosed` を無料に
し `bcCapacityRegion = closure {achievable}` との接続に効く。**第一象限制約なし** + **下方集合** の
2 点が S8-b のコストを決めた (退化被覆が約 15 行。MAC は約 420 行)。`uvInfoSum₁/₂` の**下付き数字は
受信機番号ではなく「先頭に来る corner 項の選択」**(両方とも `R₁ + R₂` の上界)。
proof-log: **yes** (`docs/proof-logs/proof-log-bc-uv-operational.md`)。

### Phase 5 — 一致するクラスを広げる 🚧 ★本線

degraded は既に閉じている。その一般化を、内界と Phase 4b の外界の組で回収する。

#### 定義段 ✅ / 内外の橋 S1–S6 ✅ (完了、1 行圧縮)

- **定義段** `2c938fe0` `91fd8dcf` `e6ff1963` `42ac21e7` (M0 在庫
  [`bc-phase5-class-inventory.md`](bc-phase5-class-inventory.md)) — `martonRegion` から
  `0 ≤ p.1 ∧ 0 ≤ p.2` を除去 (**これをやるまで等号はどのクラスでも述べられなかった**) したうえで
  `Classes.lean` を新設し 3 クラス + 包含鎖 `degraded ⊆ less noisy ⊆ more capable`
- **橋 S1–S6** `6b0c1ea1` 在庫 / `76b83bc1` `28eae4ea` / `0186b708` (M0 在庫
  [`bc-inner-outer-bridge-inventory.md`](bc-inner-outer-bridge-inventory.md)) — Marton 結合法を外界の
  `ℕ` 添字に載せ、順包含 `marton_region_subset_uv` (`@[entry_point]`) まで運んだ。**橋は `hpV` / `hK` /
  `hW` を 1 本も要求しない** (判断ログ 15)。経路変更後もこの橋は**そのまま生きている**

#### 等号 (less noisy) 🔄 — 内界を **superposition** に差し替え

M0 在庫は [`bc-lessnoisy-equality-inventory.md`](bc-lessnoisy-equality-inventory.md) (600 行、
Mathlib の壁 0 件)。**plan が次手としていた `bcOuterRegionUV ⊆ martonRegionUnionFS` は偽**と
判定され (判断ログ 18)、目標を superposition 内界に差し替えた。到達目標:

```lean
@[entry_point]
theorem bc_lessNoisy_capacity_eq_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hln : IsBCLessNoisy W) :
    bcCapacityRegion W = bcOuterRegionUV W
```

`hW` は `bc_achievability_of_rate_lt` の regularity 前提として**逆包含側だけ**に要る (順包含
`bc_capacity_subset_uv` は無条件)。`IsBCLessNoisy` は両領域を一切参照しないチャネルレベルの述語
なので load-bearing ではない。

##### S0–S7 ✅ 全段 proof done

| step | 成果 | commit |
|---|---|---|
| **S0–S2** 達成側の factor out + less noisy 接続 + 内界の集合化 | `Achievability/Assembly.lean` に `bc_achievability_of_rate_lt` (旧 `bc_achievability` の本体、**レートの符号制約を撤廃**) 系 3 本を切り出し、`SuperpositionRegion.lean` 新設。⟹ **less noisy の言葉で `bcSuperpositionRegionFullSupport ⊆ bcCapacityRegion ⊆ bcOuterRegionUV` が並んだ**。**`bc_achievability` の署名・結論は逐語不変** (監査がバイト一致で機械確認) | `06817339`…`a97fde13` |
| **S3 / S4** スロット同定 3 本 / 四つ組法 + Markov 鎖 3 本 | **41 行** (見積 90) / **74 行** (見積 140)。**どちらも自作した数学は 0 行** — S4 の親玉は既存 4 本の合成 **13 行**。前提として F-a の上流移動が要った | `102d514a` `28aafa87` |
| **S5** 有限量子化 + 裾評価 | **289 行** (見積 280)。`Quantization.lean` 新設 21 decl。F-12 リネーム同梱 | `c3508204` `89daa826` `47933abd` |
| **S6** 時分割の補助への吸収 | **545 行** (見積 440、判断ログ 20)。`SuperpositionTimeShare.lean` 新設 32 decl。**自作した数学は 3 本だけ** — `boolLaw` 一族 15 行 / `condMutualInfo_eq_mutualInfo_of_ae_const` 16 行 / **在庫に無かった** `condMutualInfo_map_uvRelabel` 14 行 | `70fc424e` `308f7c15` `dd981e01` |
| **S7** 全支持への摂動 | **802 行** (plan の粗見積 ~120 は**約 6.5 倍の外れ**。在庫 probe が着手前に ~780 行・帯 720–850 へ上方修正し実測はその帯の中、判断ログ 23)。`SuperpositionFullSupport.lean` 新設 44 decl、M0 在庫 [`bc-s7-fullsupport-inventory.md`](bc-s7-fullsupport-inventory.md) (401 行、probe 745 行が compile 通過) | `560c3399` `069c6016` |

ゲート: S0–S2 honesty **all OK** (`hsum` / `hJlt` は precondition と判定) / style **PASS**。
S3–S7 は style **PASS**、honesty は launch 条件外 (新規 `sorry` 0 / 既存署名の honesty 関連変更なし)。

⚠ **訂正 — 「摂動対象は `(pU, K)` ではなく `ν'` (時分割済の五つ組法)」は内部実装としては正しいが、
署名の高さとしては誤りだった**: S6 の到達点は `∃ k pU K, …` で `ν` を存在量化して**捨てる**ので、
法 → 法 の S7 とは合成できない。正解は **headline を対レベルに置き、対から五つ組を建て直す糊
(`uvLawOfInput` / `uvLawOfPair`、約 45 行) を内部に閉じ込める**ことで、結果として **S6 は署名変更
ゼロの黒箱**のまま残った (摂動そのものは在庫どおり五つ組の世界で行っている)。⟹ 一般則は判断ログ 23。

**S5 の成果物の署名 (消費側で機械確認した形)** — 3 本は §在庫 の行番号が SoT:

```
uvInfo₂_le_uvQuantizeLaw_add_slack    : uvInfo₂ ν ≤ uvInfo₂ (uvQuantizeLaw ν m) + uvQuantizeSlack ν m
uvInfoSum₂_le_uvQuantizeLaw_add_slack : 同型 (uvInfoSum₂)     -- こちらだけ h : IsUVChannelLaw W ν を取る
tendsto_uvQuantizeSlack               : Tendsto (uvQuantizeSlack ν) atTop (𝓝 0)
```

⚠ **仮説の非対称は意図的** — 1 本目と 3 本目は `W` も `h` も取らない。署名を揃えて使わない前提を
運ばせないための設計判断なので、S8 で「揃っていない」と見えても揃えないこと。

##### S8 📋 ★次の一手 逆包含の組み立て + headline 等号 (残り ~90 行)

証明戦略 (擬似 Lean。S7 までの実測で 3 段が既存宣言に置き換わった):

```
antisymm
  ├ ⊆ : bc_capacity_subset_uv W                             -- 既存、無条件
  └ ⊇ : intro ν hν p hp                                     -- p ∈ uvRegion ν
        U_m := 有限量子化 ; uvInfo₂ の裾を ε_m で払う               -- S5 ✅ (消費するのは S8)
        sub_mem_bcSuperpositionRegionFullSupport_of_…             -- S6 + S7 ✅ (時分割 → 摂動 → 内界へ着地)
        m → ∞ (S5 の裾) と δ → 0 (S7 の摂動) の 2 重極限 + closure  -- S8 📋
```

**S8 の入口は 2 本** (どちらも §在庫 の行番号が SoT): `(k, pU, K)` を返す
`exists_fullSupport_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw` と、内界 union への着地版
`sub_mem_bcSuperpositionRegionFullSupport_of_lessNoisy_of_isUVChannelLaw`
(`(R₁ - δ, R₂ - δ) ∈ bcSuperpositionRegionFullSupport W`)。⟹ **S8 に残るのは 2 重極限 + closure だけ**。

⚠ **第一象限を暗に仮定しないこと** (S6 で実際に発火した): 旧擬似 Lean の `λ := p.2 / b_m` は
`R₂ > 0` を暗に前提しており、実装は `R₂ ≤ 0` の枝で `h₁` (`R₁ ≤ (uvInfo₁ ν).toReal`) を DPI 1 発 +
`linarith` で使って閉じた。**`h₁` を落としていたら S6 は閉じなかった** ⟹ 外界は全平面版なので、
S8 で 3 不等式のどれかが不要に見えたら毎回点検する。

###### S8 への申し送り (S6 / S7 実装が逐語で踏んだもの)

- **S5 の 3 本 (上記の署名) を消費するのは S8** — S6 / S7 は 1 本も使っていない。凸結合の場合分けは
  probe B で機械確認済 (`nlinarith` 2 発)
- **測度を書き換える方向の `rw` は motive not type correct になる** (`condMutualInfo` が測度に依存する
  instance 引数を取るため) — `set … with h` の `h` を rw せず、`ℝ≥0∞` 値の項ごと `have` で書き換える。
  `condMutualInfo_map_comp` は無印が通る場面と `'` 版必須の場面が両方あるので**無印を `private` に
  する案は保留**
- **F-19 (`Superposition*` のサブディレクトリ昇格) は S8 と同 leg にまとめる** — 発火条件を満たし、
  §後続作業 F-21 / F-22 の重複解消が import 書換を伴うので一度で済む (在庫・実装・style の 3 者一致)
- **L-BCO9 は S7 でも不発動** (S5 / S6 / S7 の 3 段連続) ⟹ **発動判定の担い手は S8 のみ**

##### 残る 2 クラス 📋

- [ ] **more capable** (El Gamal 1979) — **「単純化」ではなく「形が違う」**。制約は 4 → 3 に減るが、
      うち 1 本 `R₁ + R₂ ≤ I(X;Y₁)` は**補助変数を含まない**新しい形で、`InBCCapacityRegion`
      (2 field) では受けきれず **3 field の新 structure が要る**。UV の `uvInfoSum₁` の
      `V = X` 特殊化で到達可能ではある。S3 / S4 / S5 はそのまま再利用できる
- [ ] **semi-deterministic** (Marton 1979) — 定義は入ったが**内界の定理が適用できない**
      (全支持仮説を定義上必ず破る、判断ログ 13) ⟹ 等号は **L-BCO7** で defer し外界側だけで止める。
      判定対象は `bc_achievability_of_rate_lt` の `hpU` / `hK` / `hW` の 3 本
- [ ] **degraded との接続は「新規配線の作成」**。`bc_converse` / `bc_achievability` はどちらも
      direct consumer 0 件で合流先の配線が存在せず、`bc_converse` の degradedness は `h_deg_block`
      (ambient 上の per-letter Markov 鎖) なので **4b の橋はそのままでは効かない** (判断ログ 11-(n))

proof-log: 定義段 / 橋 S1–S6 / S0–S7 は no。**等号 (S8) が閉じたら yes** — 書くべき要点は
判断ログ 18 (内界の選択がクラスごとに変わる) と S5 / S6 / S7 の量子化 + 時分割 + 摂動。

## 後続作業 (Phase 5 の前提ではない)

style / honesty ゲートが提起して当該 leg では見送った項目。完了したものは 1 行 + commit に圧縮して
残す (項目番号は他文書が参照するので付け替えない)。

**完了**: **A** `Assembly.lean` の二段分割 (1588 → 851 行、`210b7558`…`3af79fea`、純粋な移設で新しい
数学 0 行) / **F-a** `isMarkovChain_map_comp` を `MartonBridge.lean` (private) → `CodeToAmbient.lean:496`
(public) へ上流移動 (`102d514a` `28aafa87`、S4 の構造的前提だった) / **F-12** 四つ組法の
`IsUVChannelLaw.map_auxiliary_input_output` へのリネーム (`c3508204`、consumer 0 の間に実行)。

### B. 命名 / 死んだ宣言 (**波及がほぼ 0 の今なら事実上無料**)

1. **`bc_uv_rate_extract` (`Bridge.lean:602`、`@audit:ok`) が dead** — Assembly が
   `bc_uv_converse_slots` に乗り換えた結果 direct consumer **0**。削除 or 保持の判断が要る
2. **`*_point_mem` 5 本の命名** (`Assembly.lean` `:429` / `:565` / `:609` / `:635` / `:696`) —
   形容詞が段階を系統的に区別しておらず名前だけでは判別不能。`docs/rules/naming.md` §2 は判別子を
   仮定側に置けと定める (`bc_uv_mem_of_letterSum_le` 等)。**波及ほぼ 0**
3. `uvAux_pad_mutualInfo_prod_eq` (`Bridge.lean:723`) の `prod` が何の直積か名前から読めない
   (`uvAux_pad_pair_mutualInfo_eq` 等へ。consumer は in-file 1 件) / 4. `_cond` の位置が Mathlib 順と
   逆な `condMutualInfo_eq_of_leftInverse_cond` (`CondMutualInfoMixture.lean:66`)。どちらも優先度低

### C. 数学的な締めどころ / その他

1. **`bcConverseFanoSlack₁_le` が 2 bit 捨てている** — `Real.log (M₁ - 1) ≤ Real.log M₁` への緩和。
   converse の結論には効かないが、将来レートの残差を詰めたくなったときの最初の締めどころ
2. `bcOuterRegionUV ⊆ bcOuterRegionCoop` を示せれば「UV は協調外界より狭い」が機械可読になる (**任意**)
3. `CodeToAmbient.lean` の無タグ 7 本 + `show` → `change` の linter 警告 1 件 (別 leg)
4. **section 再配置による逐語コピーの完全畳み込み (残 ~30 行)** — `∑ i, uvInfo₁ (…)` 形への畳み込みは
   現配置では不可能 (`bcUVJointDistribution` は `uvAuxPad` に依存し、`uvAuxPad` は
   `bc_uv_converse_from_code` より**後ろ**)。取りに行くなら 2 section の上方移動が要る
5. **規約どうしが同じケースで逆方向に引く件 (本 plan の範囲外・記録のみ)**:
   `docs/rules/docstrings.md` item 1 (`## Main statements` 掲載定理には docstring 必須) と
   `scripts/lean_doc_lint.ts` の `internal-doc` ratchet (`:476`) が構造的に衝突する。**真の headline
   に `@[entry_point]` を付ける**運用で新規ファイルは ratchet 寄与 0 にできる (既定手)。
   経緯と恒久解 → **F-17**

### D. 汎用補題の置換統合 (未着手)

分割 A は**移設だけ**を行い、重複する一般形 / 特殊形の統合は手つかず。数学は増えず consumer の
書き換えだけがコストなので、着手判断は純粋に波及の大きさで決まる。

| 統合 | 被置換側の consumer (`dep_consumers.sh` 実測) |
|---|---|
| `compProd_pi_map_pair_eq_of_update_invariant` (`CodeToAmbient.lean:396`) は**同ファイル** `compProd_pi_map_pair_eq:366` の strict generalization | direct **1 decl / 1 file**、**transitive 12 decl / 2 file** (MAC `Assembly.lean` の `mac_timesharing_capacity_region` まで到達) |
| `mutualInfo_eq_of_leftInverse` (`CondMutualInfoMixture.lean:40`) は `MIChainRule.lean:35` の `mutualInfo_map_left_measurableEquiv` を subsume | direct **17 decl / 11 file** — BC 系 4 file + MAC 系 3 file + WZ 系 1 file + chain-rule 系 3 file |

**2 本目は import 面の判断が先**: consumer に `MIChainRule.lean:73` 自身が含まれるため、置換すると
**chain-rule ハブに KL-integral 依存が入る**。**1 本目 (同ファイル内で完結) だけ先に切る**のが安い。

### E. 分割 A が新たに立てた flag (優先度低)

1. **`CondMutualInfoMixture.lean` はファイル名と中身が一致していない** — 7 宣言のうち mixture は
   4 本で残り 3 本は**再符号化不変性** (tell: `Bridge.lean` は本ファイルを
   `mutualInfo_eq_of_leftInverse` のためだけに import している)。分割案 =
   `Shannon/MutualInfoReencoding.lean` + 現ファイル。consumer が既に分かれているので循環なし
2. **`open scoped BigOperators` が tree 全体で死んでいる** (同じ open を持つファイルが **189 本**) —
   tree 一括 sweep の別 leg にするのが筋で**本 plan の範囲外**

### F. Phase 5 / Phase 2 / S0–S7 が新たに立てた flag

1. **`bcJointDistribution_id_eq` (`Classes.lean:166`) のリネーム (「今が最安」)** — 裸の `_eq` で
   右辺が名前に出ず、内部橋なので docstring も無い。**consumer は同ファイル内 1 箇所のみ**。代案
   `bcJointDistribution_id_eq_map_compProd`
2. `bc_lessNoisy_infoJoint_ge` (`Classes.lean:95`) / `bc_degraded_infoJoint_ge`
   (`Achievability/Assembly.lean:967`) の `_of_` 化 — 厳密形は `bc_infoJoint_ge_of_lessNoisy`。
   **2 本同時リネームか両方現状維持かの二択** (style の推奨は現状維持)
3. 語彙橋 2 本を `private` にするか / 4. `IsBCSemiDeterministic.exists_prob_real_singleton_eq_zero`
   に `_of_one_lt_card` を付けるか (どちらも任意、優先度低)
5. **README 定理表への登録は保留** (`docs/readme-theorems.txt` は未編集)。**判断待ち**:
   `marton_region_subset_uv` / `bcSuperpositionRegionFullSupport_subset_capacity` は等号ではないが
   `bc_capacity_subset_uv` と対になる強さの `@[entry_point]` ⟹ **等号を待たず登録してよいか**
6. **リネーム束 — 4 本まとめて 1 leg**。いずれも**外部 consumer 0** (`rg` 実測) = 今が最安。
   - `auxNatIndex` → `natIndex` (中) — 定義は任意の `Fintype X` に総称で、「補助変数の」は使用側の
     ラベルにすぎない / `martonSwapLaw` → `martonAuxSwapLaw` (低) — 何を swap したか名前に出ていない
   - **`martonInfoSum` が実在しない識別子** (低) — `MartonBridge.lean:493` / `:509` の左辺は def と
     して存在せず実体はベタ書き ⟹ 読者が grep して空振りする。解消は `Marton/Setup.lean` に
     `def martonInfoSum` を新設するかリネームかの二択
   - **`FS` 略記 → `FullSupport`** (高、**未実行**) — `martonRegionUnionFS` / `_FS_subset_union` /
     `_FS_subset_capacity` の 3 本。`rg` 実測で `FS` を宣言名断片に使うのは tree 全体でこの 3 本のみ
     (**先例ゼロ**)。**新規側は既に展開形を採用済**なので、直すのは既存 3 本だけ

   **束に入れない判定が 2 件**(蒸し返し防止): (a) **`bcAuxAlphabet` は別の束** — ここでの `Aux` は
   **教科書用語の auxiliary random variable** で同族の descriptive 先例が 4 本。弁別軸は「総称なのに
   補助を名乗る (over-claim)」か「補助としてしか使われない」か。(b) **`martonRegionUnion_subset_uv` は
   family 既定と食い違っていない — 逆に既存 2 本が outlier** (`marton_region_subset_uv` /
   `marton_region_subset_capacity` だけが def 名を割っており def 名で grep すると引っかからない)。
   直すなら古い 2 本だが両方 `@[entry_point]` + 実 consumer あり ⟹ 別 leg。優先度低
7. (旧項目は F-6 のリネーム束に統合) / 8. (**§C-5 に統合**)
9. **`docs/rules/lean-style.md:29` が repo 実態と矛盾** (**本 plan の範囲外・記録のみ**) —
   「演算子は行末に置いて改行する」は複数行シグネチャの**関係記号**には当てはまっていない。継続行を
   関係記号で始める行は tree 全体で **約 5800 行 / 353 ファイル** (実測)。起票先は `docs/rules/` 側
10. **`Achievability/` クラスタ 4 ファイルの module doc タイトルが実態とずれた** (**未実行**) —
    いずれも "Degraded broadcast channel — …" のままだが S0 で assembly は**degradedness 非依存**に
    なった。4 ファイル同時のクラスタ一貫性判断なので単独では直さず flag
11. **`bc_lessNoisy_achievability` の docstring が共有コアとして `bc_achievability` を名指している**
    が、実際に共有されているのは `bc_achievability_of_infoJoint_ge`。偽ではないので未修正、優先度低
12. ✅ 完了 (上記「完了」欄)
13. `isMarkovChain_map_comp` (`CodeToAmbient.lean:496`) の引数順が兄弟 `condMutualInfo_map_comp':527`
    と非対称 (兄弟は `(ρ) (hρ)` を `f/g/h` の前、こちらは後)。呼び出し 3 箇所に波及、優先度低
14. `SuperpositionRegion.lean` の新宣言が出す `unusedDecidableInType` warning は同ファイル既存宣言と
    同じ状態 (BC 標準 variable 束由来)。直すなら family 一括の別 leg
15. **汎用補題が BC namespace に居る (S5 / S6 / S7 の style ゲート、推奨度 高。S7 で +4 = 計 9 本)** —
    `Quantization.lean:59` / `:66` / `:81` の `mutualInfo_ne_top_of_fintype_right` /
    `mutualInfo_le_ofReal_log_card` / `mutualInfo_eq_zero_of_ae_const` と、
    `SuperpositionTimeShare.lean:58`–`:70` の `boolLaw` 一族 3 本 (`boolLaw` /
    `boolLaw_isProbabilityMeasure` / `lintegral_boolLaw`) + `:186` の
    `condMutualInfo_eq_mutualInfo_of_ae_const`、`SuperpositionFullSupport.lean:257` / `:262` / `:267` /
    `:616` の `boolLaw_real_true` / `boolLaw_real_false` / `entropy_eq_binEntropy_of_map_boolLaw` /
    `exists_perturb_weight` (style が S7 の 44 decl を全走査して過不足なしを確認。**`exists_perturb_weight`
    の改名は移設と同時にやる**のが筋 = 今やると二度手間)。いずれも BC 固有の語を 1 つも含まない汎用 API で、
    **次に同じ補題を探す人は `BroadcastChannel/` を見ない** (CLAUDE.md「In-repo asset search」の
    失敗モード直撃)。移動先候補は `Shannon/MutualInfo.lean` / `Shannon/CondMutualInfo.lean` /
    `Shannon/CondMutualInfoMixture.lean` / 確率ユーティリティで、**import 循環の検討が要る一括タスク**
    (判断ログ 11-(i): 移動先は consumer ではなく `entropy_le_log_card` と
    `mutualInfo_eq_entropy_sub_condEntropy` の**両方**に届く位置で決まる)。`boolLaw` は移設するなら
    名前も再考 (BC namespace 直下では総称的すぎる。`bernoulliClamped` 等)。波及の実測は
    `mutualInfo_ne_top_of_fintype_right` が direct **8 decl / 2 file**
    (`dep_consumers.sh`)。`condMutualInfo_map_uvRelabel` は `uvRelabel` を主語にするので**対象外**
16. ✅ 決着 — `Quantization.lean` の orphan 懸念は S6 が解消した。`SuperpositionTimeShare.lean` が
    同ファイルの 4 本 (`mutualInfo_ne_top_of_fintype_right` / `mutualInfo_eq_zero_of_ae_const` /
    `uvInfo₂_ne_top` / `uvInfoSum₂_ne_top`) を消費する ⟹ **外部 consumer 0 件ではなくなった**。
    S5 の裾評価 3 本は S8 が消費する
17. **§C-5 の規約衝突が S7 で 4 度目の発火。ただし今回は機構が特定された** (本 plan の範囲外・記録のみ)
    — 再燃の原因は**規約文が決着に追随していないこと**: 実効ルールは S6 で「**docstring 必須は
    `@[entry_point]` headline**、`@[entry_point]` の無い Main statements エントリは name-adequacy で
    bare」と言語化されたのに、`docs/rules/docstrings.md` item 1 の括弧が旧文言のまま。**恒久解は
    item 1 の括弧を `@[entry_point]` のみに直すこと**。起票先は `docs/rules/` 側 (本 plan からは編集しない)
19. **`Superposition*` クラスタのサブディレクトリ昇格 (推奨度 高、S8 と同 leg)** — **発火条件を
    満たした**: 3 ファイル 1556 行 (Region 209 / TimeShare 545 / FullSupport 802)。在庫・実装・style の
    3 者が「**S8 と同 leg にまとめる**」で一致 (F-21 / F-22 の重複解消が import 書換を伴うため一度で
    済む)。先例は `OuterBoundUV.lean` umbrella + `OuterBoundUV/` 6 ファイル
20. **内ループの `lake env lean` は一部の linter に盲目 (検証の穴)** — S7 で**実測が裏付けた**:
    `lake env lean` が完全に沈黙するのに `lake build` は `linter.flexible` / `linter.style.show` /
    `unusedDecidableInType` を計 19 件出した。⟹ **実装 leg の検証バーに `lake build <module>` を
    含めるのを family の既定手にする**。個々の warning の掃除は F-14 と同じ family 一括の別 leg
21. **重複 A: `uvConstLaw` (`OuterBoundUV/Region.lean:401`) は S7 の `uvLawOfInput` の dirac 特殊化**
    (style ゲートが probe で機械確認、散文だけの主張ではない) — `uvConstLaw W x₀ = uvLawOfInput W
    (Measure.dirac ((0:ℕ), (0:ℕ), x₀))` が **`rfl` で通る**。加えて S7 の private
    `measurable_uvUnassoc` は `Region.lean:409` の private 版と**証明項まで逐語同一** (S7 版が一般形)。
    `Region.lean` は S7 の import 閉包内なので **import 変更なしで畳める** — `uvLawOfInput` を上流へ
    移せば Region 側 4 decl (~45 行) が消える
22. **重複 B: S6 の分岐クラスタは S7 の一般混合の特殊化** (同じく機械確認) —
    `uvTagConst ν u₀ = uvTagFalse (ν.map (uvRelabel (fun _ ↦ u₀) id))` が成り立ち、
    `uvBranchKernel` / `uvTimeShareLaw` は `uvMixKernel` / `uvMixLaw` の特殊化で、対応する 3 本が
    **証明本体まで逐語重複** (~60 行削減)。**在庫が事前に指摘していたが実装が畳まなかった側**

以下は橋 S5 / S6 の style ゲートが提起 (F-a は完了済):

- **F-b: `mutualInfo_le_add_condMutualInfo` (`MartonBridge.lean:329`、private、8 行) を
  `Shannon/CondMutualInfo.lean` へ上流移動** — BC 固有要素ゼロの教科書的不等式で **import 書換ゼロ**。
  **条件付き版が `OuterBoundUV/Gateway.lean:194` に public + `@audit:ok` で既存**なので、無条件版が
  private で 2 ファイル離れて埋まっている状態は「既に書いたか」失敗モードの温床
- **F-d: public / private の非対称 (API 面、人の判断待ち)** — `martonInfoV₁V₂_eq_mutualInfo_toReal:252`
  は public かつ `## Main statements` 掲載なのに、完全な兄弟 `:375` / `:386` は private

## 未解決本体との距離 (正直な見積り)

「Marton 内界 = 一般 BC の容量領域か」は **open**。数学が存在しないので形式化できない。本計画が
終わっても未解決問題は未解決のままで、得られるのは (a) 内界・外界・容量領域が同一言語で並び
**ギャップが機械可読な形で固定される**、(b) 特定の BC で内外が分離するかを検証する基盤 (**既に 1 度
使われた**、判断ログ 18)、(c) 一致が既知の特殊クラスで等号が実際に閉じる (Phase 5)、の 3 点。
期待値は「厳密な足場 + 教材価値」に置くのが妥当。

## 設計上の未決事項

1. **補助変数 union の射程** (Phase 2) — **濃度固定で止める形で決着**。情報理論側の Carathéodory
   (支持補題) は書かない (Fenchel–Eggleston が Mathlib 不在ゆえ自作行数が跳ねる)。残る判断は P7 を
   取るかだが、**等号の前提ではなくなった**
2. **more capable の容量領域を受ける structure** (Phase 5) — 3 制約 (うち 1 本は補助変数を
   含まない `R₁ + R₂ ≤ I(X;Y₁)`) なので `InBCCapacityRegion` を拡張するか新 structure を建てるか
3. **`martonInfo*` を `ℝ≥0∞` 版へ pivot するか** — **less noisy の等号からは外れた**。superposition
   路では `I(V₁;V₂)` (補助 × 補助) が現れず 4 スロットすべてが出力との情報量なので `.toReal` の
   危険が構造的に発火しない ⟹ **Marton union の API を完成させたくなったときだけの判断**。
   `uvRegion` 側の同じ問いは決着済 (有限アルファベットでは無関係)

## 撤退ライン (frozen slug)

| slug | 発動条件 | 退避先 |
|---|---|---|
| **L-BCO1** | Phase 4 の補助変数 identification が閉じない | **不発動** (Phase 4a) |
| **L-BCO2** | Phase 2 の型量化 union が universe 問題で詰む | 濃度固定版で止め union は取らない。**不発動** — 問題は union の定義側ではなく**消費側** (`IsBCLessNoisy` が `U : Type u` を量化) にあり `bcAuxAlphabet = ULift.{u} (Fin (k+1))` が **0 行で吸収**した。**P6 (付け替え不変性) が閉じたら「答えた」になる** |
| **L-BCO3** | Phase 5 の等号が Phase 4 の外界の形と噛み合わない | クラス定義だけ入れて等号は defer。**発動条件の文言は実態とずれている** — 噛み合わなさの本体は外界の形ではなく**内界の形**だった (符号制約 = `2c938fe0` で解消 / 内界の選択 = 判断ログ 18 で superposition へ / 全支持仮説 = L-BCO7)。slug は凍結なので文言は残し、判定は内界側の 3 点で行う |
| **L-BCO4** | Phase 4b の符号→ambient 橋または単一文字還元が閉じない | **不発動のまま Phase 4b が完遂** |
| **L-BCO5** | S5 の補助変数の型統一が `mutualInfo_chain_rule` 経由でも閉じない | **不発動** (在庫の攻略路がそのまま効いた)。退避先だった `bcOuterRegionUVAt W n` + `⋂ n` 版は採らない |
| **L-BCO6** | S8-b の退化レート被覆が MAC 同様 450 行級に膨らむ | **不発動** — 全平面版で closure した (退化被覆は約 15 行) |
| **L-BCO7** | semi-deterministic の等号を狙う段で、内界の達成側の全支持仮説が外せない (判断ログ 13) | **semi-deterministic はクラス定義 + 外界側だけで止め、等号は述べない**。外界 (`bc_capacity_subset_uv` の特殊化) は `hW` を要求しないので単独で成立する。退避の出口は `sorry` + `@residual(plan:bc-semideterministic-fullsupport)`。**`IsSemiDeterministicAchievable` のような述語に核を束ねる形は取らない**。**判定対象は経路変更で移った** — 旧: `marton_achievability` の `hW` / 新: `bc_achievability_of_rate_lt` の `hpU` / `hK` / `hW`。橋 S1–S6 は全支持仮説を 1 本も要求しない (判断ログ 15) ので本ラインの外 |
| **L-BCO8** | (**⚠ 無効化**。逆包含 `bcOuterRegionUV ⊆ martonRegionUnionFS` が**偽**と判定され枠組みごと失効、判断ログ 18) | **⚠ 使用禁止** — 旧退避先「`sorry` で署名を保つ」は偽の命題を署名に残すことになり取れない (CLAUDE.md 検証の誠実性)。後継は **L-BCO9** |
| **L-BCO9** | (凍結文言) less noisy の等号で **S6 (時分割の補助への吸収) が閉じない**。⚠ **S5 / S6 / S7 の 3 段連続で不発動が確定** (`c3508204` / `70fc424e` / `560c3399` で proof done) ⟹ **発動判定の担い手は S8 (組み立て) のみに移った**。以後は「逆包含が閉じない」と読む | 逆包含 `bc_uv_subset_superposition : bcOuterRegionUV W ⊆ bcSuperpositionRegionFullSupport W` を **署名を保ったまま** `sorry` + `@residual(plan:bc-lessnoisy-converse-quantization)` で残し (後継 plan のファイル名 stem)、S0–S7 の成果だけで leg を閉じる。この時点でも `bcSuperpositionRegionFullSupport W ⊆ bcCapacityRegion W ⊆ bcOuterRegionUV W` の挟み込みが **less noisy の言葉で** 1 本立つので単独で価値がある。**`IsLessNoisyTight` / `IsSuperpositionOptimal` のような「等号が成り立つ」を束ねる述語は作らない** |

**active な撤退ラインは L-BCO2 / L-BCO3 / L-BCO7 / L-BCO9 の 4 本**。L-BCO8 は無効化 (履歴として残置)。

**禁止事項**: どの撤退でも「外界が成立する」「補助変数が取れる」「符号から ambient が取れる」等を
`*Hypothesis` 述語に束ねて仮説として渡す形は取らない (CLAUDE.md 検証の誠実性 tier 5)。退避は
`sorry` + `@residual` で、署名は証明したい形のまま保つ。**ただし偽と判定された命題は署名としても
残さない** (L-BCO8 の教訓) — 偽の署名に `sorry` を置くのは充填不能な `sorry` を作ることであり、
その場合は退避ではなく**目標の差し替え**が正しい手。Phase 5 で等号を述べる段では、クラス条件
(less noisy 等) を「等号が成り立つ」に近い形の述語で受け取っていないかを毎回確認する。

## 推奨実行順

内界を superposition に差し替えたうえで、**残るは逆包含 1 本**:

```
Phase 5 定義段 ✅ → 内外の橋 S1–S6 ✅ → Phase 2 最小完遂 P1–P3 ✅
  ↓                                        (Marton union の順包含はここで確定。以降も生きている)
S0 達成側の factor out ✅ → S1 less noisy 接続 ✅ → S2 内界の集合化 ✅
  ↓  bcSuperpositionRegionFullSupport ⊆ bcCapacityRegion ⊆ bcOuterRegionUV が less noisy で並んだ
S3 スロット同定 ✅ → S4 Markov 鎖 + 四つ組法 ✅ → S5 量子化 + 裾評価 ✅ (S3–S5 は more capable で再利用可)
  ↓  S6 時分割 ✅ → S7 全支持摂動 ✅ = 外界の 3 不等式から**全支持の対**を構成し内界へ着地する 1 本まで到達
S8 逆包含 + 等号 ★次の一手 (詰んだら L-BCO9。F-19 のディレクトリ昇格 + F-21 / F-22 の重複解消を同 leg に)
more capable の等号 (3 field の新 structure、S3 / S4 / S5 を再利用) → semi-deterministic は L-BCO7
```

**S8 の dispatch も在庫 leg から始める** (probe を厚く取る根拠は判断ログ 20 / 23。ただし**行数見積りは
数学と散文・section 構造を別枠で積む**)。**Phase 2 の P4–P7 / §後続作業 B–F は S8 の前提ではない**
(F-1 / F-6 リネーム束のみ consumer が 0 の今が最安。**F-19 / F-21 / F-22 だけは S8 と同 leg**)。

## 判断ログ

9. **`IsUVChannelLaw` は load-bearing hyp ではなく包含の右辺を縮める構造条件** (監査判定): union を
   無制約に取ると出力を入力にコピーする `ν` が 4 スロットを任意に大きくでき、**外界が平面全体に
   退化して `bc_capacity_subset_uv` が vacuous に真になる**。`isUVChannelLaw_iff` が「union の添字は
   補助と入力の任意の同時法をチャネルに通したもの ちょうど」を与えて反例 class ごと閉じている。
   **外界の形を触るときはこの特徴づけが壊れないかが最初のチェック点** (S4 / S5 はどちらもこの
   特徴づけから欲しい性質を出して通過 = 消費側でも十分に強かった)。
11. **在庫予測の外れ (通算 23 件) — 在庫ファイル自体は編集しないので本エントリが記録の SoT**。
    生きた教訓のみ残す (settled な個別項目は git):
    - **(f) 雛形を参照するときは「その雛形の到達目標が自分と同じ強さか」を先に確認する** —
      「MAC の約 420 行が退化レート被覆の雛形」は誤りで、MAC はそもそも退化レートを被覆していない。
      **S6 で再発が予告されている** (`bcUVTimeShare` は `Fin n` 一様混合に張り付いていて重み `λ` を
      取れない)。
    - **(g) 前 step の到達点が次 step の入口として使えるとは限らない** — 縮小点の**加法形**は極限に
      乗らない。**乗法形**への差し替えで解決。step 境界では結論の**形**を独立に確認する。
    - **(i) import の必要性は consumer 表ではなく移動先の依存の閉包で決まる** (分割 A の 3 件 +
      4 度目 = F-a、**5 度目の候補が F-15**: 汎用 3 本の移動先は consumer ではなく
      `entropy_le_log_card` / `mutualInfo_eq_entropy_sub_condEntropy` の**両方**に届く位置で決まる)。
    - **(k) 「独立」「park 可」の判定は到達目標ごとに違う** — park 判定は目標を名指して書く。
      Phase 2 は「等号の前提」だったが内界が superposition に移って前提でなくなった ⟹
      **目標側が差し替わると依存関係の宣言は失効する**。
    - **(l) more capable は「単純化」ではなく「形が違う」+ 文献帰属が 1 件誤り** — less noisy は
      **Körner–Marton 1975/1977** (El Gamal 1979 は more capable)。制約は 4 → 3 に減るのに
      `R₁ + R₂ ≤ I(X;Y₁)` が補助変数を含まない新形ゆえ受け皿の structure は新設が要る。
    - **(n) 「同じ floating 形だから橋が効く」は形の一致であって仮説の一致ではない** —
      `bc_converse` の degradedness は `h_deg_block` で、対応版は 0 hit、新規 ~120 行が要る。
      再利用可否は結論形ではなく**要求される仮説の表現**で決まる。
    - **(o) 在庫の依存の向きが 1 本ずれた (S5)** — 「`uvInfo₂` の有限性は DPI 経由でしか出ない」は
      誤りで、片側有限性 `mutualInfo_ne_top_of_fintype_right` を先に入れればチャネル法を使わず直接
      出る。**「S5-a を gateway-atom として先に切る」という順序判断は正しく、理由だけがずれていた**
      ⟹ 実装時は在庫の *順序* だけ引き継ぎ、*理由* は自分で引き直す。
13. **semi-deterministic は内界の定理と構造的に非両立 (L-BCO7 の根拠)**: 達成側の全支持仮説
    `hW : ∀ a b, 0 < (W a).real {b}` を **semi-deterministic は定義上必ず破る** (`Y₁ = f(X)` ゆえ
    到達しない出力対の質量が 0。in-tree の証拠は
    `IsBCSemiDeterministic.exists_prob_real_singleton_eq_zero`)。superposition 路でも全支持は要る
    ので内界を差し替えても解消しない。⟹ 一般教訓: **「文献で容量領域が既知」と「in-project の内界
    定理が適用できる」は別** — クラスを候補に挙げる前に既存定理の regularity 前提との両立を見る。
15. **橋は内界側の全支持仮説を 1 本も要求しない ⟹ L-BCO7 は緩む方向 (S1–S6 を通じて不変)**:
    明示仮説は `pV` / `K` / `W` と型クラスだけ (署名走査で実測)。⟹ 一般教訓: **撤退ラインは「どの
    宣言が止まるか」まで降ろして書く**。「クラス X では内界が使えない」の粒度だと、無関係な後続
    step まで巻き込んで park することになる。
16. **在庫が「無いので自作する」と書いた資産は、実装着手時に両方の検索軸で引き直す (3 leg 連続で
    発火)**: (a) 橋 S5 の条件付き DPI `condMutualInfo_le_of_markov_joint` は要求どおりの形で存在
    (当てたのは**名前検索**、結論形検索では出なかった)。(b) S0–S2 の一般形
    `entropy_measurableEquiv_comp` (`Shannon/Pi.lean:36`) は既に import 閉包内。(c) S4 の「Markov 鎖を
    出す既存補題は 0 件」は**核についてのみ正しく、部品は全部在った** (既存 4 本の合成 13 行)。
    ⟹ **在庫段階の 0-hit は検索軸に依存する** + **「既存補題 0 件」は合成しうる部品の不在を
    意味しない** — 0-hit を見たら次は「1 段分解した各辺」で引き直す。
18. 🔄 **内界の選択はクラスごとに変わる — `martonRegionUnion` は劣化 BSC 対ですら容量領域より真に
    小さい (経路変更)**: `bcOuterRegionUV ⊆ martonRegionUnionFS` は**偽**で、さらに corner 点が
    `bcCapacityRegion` に入るので **劣化 BSC 対ですら `martonRegionUnionFS ⊊ bcCapacityRegion`**
    (数値と再検証コマンドは [`bc-facts.md`](bc-facts.md))。原因は共通補助 `U₀` の不在で、`U₀` は
    `martonRegion` の署名に**入る余地がない** (足すのは符号化定理からの作り直し = Phase 5 の射程外)。
    ⟹ 内界を superposition に差し替え、L-BCO8 を無効化し L-BCO9 を新設した。⟹ **一般教訓 2 つ**:
    (a) **plan が「⚠ 正直な限界」として書いた但し書きは、最も素直なクラスで実際に発火しうる**
    (どのクラスで発火するかまで詰めないと、下流に建てた目標が丸ごと偽になる)。(b) **「内界 ⊆ 容量
    領域」を持つことは「その内界で等号が狙える」を意味しない** — 等号の相手として使う前に、既知の
    到達点がその内界に入るかを 1 度数値で当たる。
20. **S6 の実測が在庫予測を 2 つの粒度で外した (見積りの粒度 / 雛形の粒度)** — どちらも S8 で
    同型が出るので次 leg の判断材料:
    - **(a) 在庫の probe 行数は「数学の行数」を予測するが「ファイルの行数」は予測しない**。
      S5 = probe 147 行 → 見積 280 / 実測 289 (的中)、S6 = probe 295 行 → 見積 440 / 実測 545
      (**+24%、帯を上振れ超過**)。**超過分の主因は数学ではない** — 数学の中身は probe 295 行が
      ほぼそのまま乗り、増分は module doc 42 行 + `omit` を最小化するための `variable` 束 8 分割。
      ⟹ **見積りは「数学」と「散文・section 構造」を別枠で積む**。
    - **(b) 雛形の再利用可否は「宣言」と「証明骨格」で別々に判定する** (11-(f) の S6 での決着)。
      `bcUVTimeShare` は予告どおり**宣言としては再利用不可**だった (`Fin n` 一様混合に張り付き重み
      `λ` を取れない) が、**証明骨格は逐語で効き S6 で最も時間を節約した資産**になった。plan は
      「写経ではない」とだけ書いて後者を落としていた ⟹ **雛形を却下するときは「宣言 / 骨格」の
      どちらを却下したのかまで書く**。
21. **却下は「この step では」と限定して書く (20-(b) の同型、S7 で発火)**: S6 の在庫が「外れ」と
    判定した `IsUVChannelLaw.condMutualInfo_le_map_cond` (`Quantization.lean:126`) が、S7 では
    **粗視化の向き**でそのまま当たり、スロット 1 が**罰則ゼロ・5 行**で閉じた。⟹ 一般則:
    **却下の射程を step に限定する** — 「この補題は当たらない」ではなく「この step の向きでは
    当たらない」と書けば、次の step が同じ資産を引き直せる。
22. **スロット 2 の加法ペナルティ (`Real.binEntropy`) は証明技法の都合ではなく命題の性質**:
    乗法だけの下界 (`≥ (1-ε)·orig`) は**偽**で、在庫が数値反例を持っている (`U = X = Y₂ = Bool`、
    `X = U`、`W₂` 恒等、ε = 0.01)。⟹ **どんな凸性補題からも出ない**ので、
    `RateDistortion/Convexity.lean:336` の `klDiv_mixture_le` 系を探しに行かせないこと。
    タグ変数の分だけ相互情報量が増えうるのだから、加法項は摂動の構造そのものが要求している。
23. **plan の粗見積りは在庫 probe で必ず上書きする (S7 で 6.5 倍の外れ)**: plan の `~120 行` に対し
    在庫 probe が ~780 行・帯 720–850 と判定し、実測 802 行は**在庫の帯の中**に入った。
    ⟹ **probe を持たない見積りは桁で外れうる** (20-(a) が「probe があれば数学の行数は当たる」を
    示したことの裏面)。同じ leg で**署名の高さの予測も外れた**: plan の「摂動対象は `(pU, K)` では
    なく `ν'`」は内部実装としては真だが、S6 の到達点が `ν` を存在量化して捨てるため法 → 法では
    合成できず、headline は対レベルに置かざるを得なかった ⟹ **step をまたぐ設計判断は「何を
    摂動するか」ではなく「前 step の到達点が何を返すか」で決まる** (11-(g) の署名版)。
