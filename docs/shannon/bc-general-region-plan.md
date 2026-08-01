# Shannon: 一般 BC 容量領域フレーム サブ計画

> **Parent**: [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md) §L-BC5 後続

未解決問題「一般 2 受信者 BC の容量領域の特徴づけ」に対して形式化が提供できるのは **足場**
(内界 / 外界 / 両者による挟み込み) までで、未解決本体 (内外一致) は数学が存在しないので Phase 外。
本計画はその足場を組む。到達目標は `内界 ⊆ bcCapacityRegion ⊆ 外界` を Lean の 1 本の定理列として
持ち、一致が既知のクラスでは等号まで閉じること。確定事実の台帳は
[`bc-facts.md`](bc-facts.md) (再導出が高価なものだけ。機械で安いものは毎回引き直す)。

**参照規約**: ファイルは `Shannon/` からの相対パス、宣言は名前で指す。**行番号・行数・宣言数は
書かない** (`docs/rules/module-structure.md` §参照規約 + 判断ログ 26 — いずれも再配置のたびに
無効化されるキャッシュで、安定したハンドルは宣言名のほう)。

## 進捗

**全 Phase 完遂**。実作業として残るのは §後続作業 のうち B-3 / B-4 / C-1 / C-2 / C-4 / D-2 /
E-2 / F-14 / F-23 / G-1 のみで、いずれも到達目標の前提ではない。

- [x] Phase 1 操作的容量領域 (主語) ✅ `fd39ad95` `deb930a7`
- [x] **Phase 2 補助変数 union ✅ 完遂** — 最小完遂 P1–P3 `fcdafaf5` `b1837901` /
      拡張 P4–P6 `64a2d6ab` `d0c02420` / P7 `fd41037e` `813d1cfd` `93a3a6fb`。
      **等号の前提ではなくなっていた** (経路変更、判断ログ 18) が API としては完成した
- [x] Phase 3 協調外界 (安い外界) ✅ `e9222d0a` `b9ba272a`
- [x] Phase 4a UV 単一文字化 (floating 形) ✅ `5bf64adf`…`54705cb3`
- [x] Phase 4b UV 外界の集合化 + 操作的包含 ✅ `6ddb1a48` `bfdd55e1` `c768cc00` (**全平面版**)
- [x] **Phase 5 一致クラスの拡張 ✅ 完遂** — 残作業なし
  - [x] 定義段 (符号規約の対称化 + 3 クラス + 包含鎖) ✅ `2c938fe0`…`42ac21e7`
  - [x] 内外を同じ添字に載せる橋 S1–S6 ✅ `6b0c1ea1`…`28eae4ea`
  - [x] **less noisy の等号 ✅ 到達** — 内界は Marton union ではなく **superposition**。
        S0–S8 全段 proof done (`06817339`…`558b3fca`)。頂点は `@[entry_point]`
        `bc_lessNoisy_capacity_eq_uv : bcCapacityRegion W = bcOuterRegionUV W`
  - [x] **more capable の等号 ✅ 到達** — `4a01dff8`…`594887a4`。頂点は `@[entry_point]`
        `bc_moreCapable_capacity_eq_uv`。**less noisy の等号を包含する** (§Phase 5)
  - [x] **degraded との接続 ✅ 完遂** `bf49a91d`…`86b90af1` — 古典形 converse を符号に着地
        (`bc_degraded_converse_from_code`)。semi-deterministic は L-BCO7 で判断済 = 新規作業なし

## 在庫

| 資産 | 場所 | 用途 |
|---|---|---|
| `BCAchievable` / `bcCapacityRegion` | `BroadcastChannel/Operational.lean` | 主語。包含の左辺 |
| `bc_capacityRegion_isClosed` / `bc_achievable_mono` / `bc_mem_closure_of_strictly_below` | 同上 | 閉性・down-set 性・厳密不等号からの closure 回収 (3 本目が内界包含の主役) |
| `martonRegion` / `bc_strict_interior_achievable` / `marton_region_subset_capacity` | 同上 | Marton 内界の集合版と包含 (`@[entry_point]`)。**符号制約なしの全平面版** (`2c938fe0`) |
| **比較クラス 3 本 + 包含鎖** | `BroadcastChannel/Classes.lean` | `IsBCLessNoisy` / `IsBCMoreCapable` / `IsBCSemiDeterministic` と `@[entry_point]` 4 本 `bc_lessNoisy_infoJoint_ge` / `IsBCDegraded.isBCLessNoisy` / `IsBCLessNoisy.isBCMoreCapable` / `IsBCSemiDeterministic.exists_prob_real_singleton_eq_zero_of_one_lt_card`。語彙橋 2 本 `bcJointDistribution_id_eq_map_compProd` / `mutualInfoOfChannel_map_eq_mutualInfo_bcJointDistribution` は F-3 で private。**`IsBCLessNoisy` は `∀ (U : Type u) [Fintype U]` を量化する** ⟹ 達成側に渡す補助は有限型でなければならない (S5 の量子化の理由) |
| `IsBCDegraded` | `BroadcastChannel/Basic.lean` (F-29 で移設) | 劣化性。def が要求する型クラスは `[MeasurableSpace]` 3 本のみ |
| `bcOuterRegionCoop` / `bc_capacity_subset_coop` | `BroadcastChannel/OuterBound.lean` | 協調外界と包含 (`@[entry_point]`)。挟み込みの右辺その 1 |
| `BroadcastCode.restrict₁/₂` / `coop` + 誤り確率補題 | 同上 | BC 符号 → 単一ユーザー符号への 3 通りの還元 |
| `channelCoding_operational_rate_le_capacity` | `ChannelCoding/StrongConverseAsymptotic.lean` | 操作的レート ≤ 容量 (`@[entry_point]`)。Phase 3 の心臓 |
| `uvAux` / 単一文字化 4 本 / `InBCOuterRegionUV` / `bc_uv_converse` | `BroadcastChannel/OuterBoundUV.lean` | Phase 4a。`uvAux` の**型が letter `i` に依存する**のが S5 の型統一の理由。headline は degradedness 前提なし (`@[entry_point]`) |
| **符号→ambient の共有層** | `ChannelCoding/CodeToAmbient.lean` (MAC/BC 共有) | `isMarkovChain_of_compProd_pi` / `isMemorylessChannel_of_compProd_pi` / `le_log_of_ceil_exp_le` + BC 由来の汎用 3 本 (`compProd_comap_map_prodMap` / `compProd_pi_map_pair_eq_of_update_invariant` / `le_toReal_of_inv_mul_le`) + `isMarkovChain_map_comp` (F-a で上流移動、F-13 で引数順を兄弟 `condMutualInfo_map_comp'` に合わせた) + **degraded 接続が足した汎用 5 本** `pi_map_comp_of_injective` / `compProd_map_prodMap` / `measure_singleton_eq_mul_of_append` / `piBlockKernel` + instance / **`pi_map_unzip_eq_compProd`** (gateway atom = pi 積の二段分解) |
| **ブロック版 degradedness → 符号への着地** | `BroadcastChannel/DegradedFromCode.lean` | `bcConverse_block_append` (出力ブロック全体を `piBlockKernel` で append) → `bcConverse_prefix_append` (`Fin i ↪ Fin n` で前置ブロックへ再添字) → **`bcConverse_degradedBlock`** (`IsBCDegraded W` から `bc_degraded_converse` の `h_deg_block` を出す = §存在しないもの (d)) → `@[entry_point]` **`bc_degraded_converse_from_code`** (古典形 converse を `bcConverseAmbient c W` に着地。**残る明示仮説は `hdeg : IsBCDegraded W` と `2 ≤ M₁` / `2 ≤ M₂` だけ**) |
| append 型 Markov 鎖の汎用 2 本 | `Shannon/CondEntropyMemoryless.lean` | `kernel_compProd_prodMkRight_eq_prod` / `isMarkovChain_of_append`。**`Achievability/Assembly.lean` の `private` を解除して上流移設** (`bf49a91d`) |
| **BC の符号→ambient 橋 + UV per-letter 情報スロット** | `BroadcastChannel/OuterBoundUV/Bridge.lean` | `bcConverseAmbient` → 構造前提 4 本 → `bcConverseFanoSlack₁/₂` → `bc_uv_converse_from_code` → `uvAuxPad` + 不変性。`section PerLetterInfo` が 4 スロット `uvInfo₁` / `uvInfo₂` / `uvInfoSum₂` / `uvInfoSum₁` + **第 3 スロット `uvInfoJoint`** (`= I(X;Y₁)`、どちらの補助も見ないので 4 スロットの後ろ。F-28) + 総称形 `mutualInfo_pair_out₁_eq_uvInfoJoint` + `bcUVTuple` / `bcUVJointDistribution` + 同定 4 本 |
| **UV 外界の集合版** | `BroadcastChannel/OuterBoundUV/Region.lean` + `OuterBoundUV/Assembly.lean` | チャネル整合条件 `IsUVChannelLaw` + 特徴づけ `isUVChannelLaw_iff` + 閉包性 5 本 + `.map_auxiliaries` / `.swap_auxiliaries` / `.map_input_output`。領域 `uvRegion` / `bcOuterRegionUV` / `_isLowerSet` / `_isClosed` / `_nonempty`。非退化の証拠 2 本。**`section Law` = 対 → 五つ組の糊 `uvLawOfInput` 一族** (F-21 で S7 から上流移動し、`uvConstLaw` はその dirac 特殊化になった)。符号側の支払い `bcUVJointDistribution_isUVChannelLaw` だけ `Assembly.lean` |
| **S4 = 四つ組法 + Markov 鎖 3 本** | 同 `Region.lean` `### The Markov chains carried by a channel law` | `IsUVChannelLaw.map_auxiliary_input_output` (四つ組法、仮説は `[IsMarkovKernel W]` + `[SFinite ν]` のみ) / 親玉 `.isMarkovChain_UV_X_Y` (結論は **出力対のまま** `(U,V) → X → (Y₁,Y₂)`) / `.isMarkovChain_U_X_Y₁` / `.isMarkovChain_V_X_Y₁`。**Markov 鎖 3 本の `section Transport` は `[StandardBorelSpace _] [Nonempty _]` を 5 型すべてに + `[IsProbabilityMeasure ν]` を要求する** (四つ組法は要求しない) |
| **S5 = 補助の有限量子化** | `BroadcastChannel/OuterBoundUV/Quantization.lean` | `uvQuantize` (`ℕ → ULift.{u} (Fin (m+1))`、切詰め) / `uvQuantizeLaw` / `uvQuantizeSlack` (`= ν {q \| m ≤ q.1} * ENNReal.ofReal (Real.log (Fintype.card β₂))`) / `_isUVChannelLaw`。**S8 が消費する裾評価 3 本** = `uvInfo₂_le_uvQuantizeLaw_add_slack` / `uvInfoSum₂_le_uvQuantizeLaw_add_slack` / `tendsto_uvQuantizeSlack`、**同じく S8 が消費する 2 本** = `uvInfo₁_uvQuantizeLaw` (量子化はスロット 1 を**等式で**保つ) / `uvQuantizeSlack_ne_top`。有限性 `uvInfo₂_ne_top` / `uvInfoSum₂_ne_top` と、任意の可測 `f : U → U'` に一般化された `IsUVChannelLaw.condMutualInfo_le_map_cond` |
| **時間共有 + 平均化 + 極限 + headline** | `BroadcastChannel/OuterBoundUV/Assembly.lean` | 混合法 `bcUVTimeShare` (+ `_isUVChannelLaw` / `_eq_sum`) と 4 スロット平均化 `bcUVTimeShare_uvInfo₁_ge` 系。再ラベル一族 `uvRelabel` (S5 / S6 / S7 が全部使う。`uvInfoSum₂_map_uvRelabel` は `[Fintype U]` を要求。**`uvInfo₁_map_uvRelabel` が `e₂ := id` で量子化に等式のまま当たる** = S8 のスロット 1 の担い手。`uvInfoJoint_map_uvRelabel` が more capable の第 3 スロット版)。縮小点の**乗法形** `bc_uv_rate_sub_fanoSlack_mem_of_ceil_exp_le` → `bc_uv_rate_mem_of_mul_le_logCard` → `bc_uv_rate_mul_one_sub_mem_of_errorProb_le` → `bc_uv_quadrant_mem_of_achievable` → headline `bc_capacity_subset_uv` (`@[entry_point]`。B-2 で 5 本とも `_of_<仮説>` 軸へ改名) |
| 汎用資産 (BC 非依存、自作) | `Shannon/MutualInfoReencoding.lean` / `Shannon/CondMutualInfoMixture.lean` (E-1 で分割) | 再符号化不変 3 本 `mutualInfo_eq_of_leftInverse` / `mutualInfo_congr_ae` / `condMutualInfo_eq_of_leftInverse_cond` + 混合法 3 本 `condMutualInfo_compProd_fst_eq_lintegral` / `mutualInfo_compProd_eq_add_lintegral` / `condMutualInfo_compProd_snd_eq_lintegral` (**S6 の核**)。混合法は**絶対連続性の仮説を持たない等式** |
| 汎用資産 (F-15 で BC namespace から昇格) | `Shannon/MutualInfoFiniteRange.lean` / `Shannon/BoolLaw.lean` / `Probability/Mixture.lean` / `Probability/SingletonMass.lean` | 有限値域の MI 4 本 (`mutualInfo_ne_top_of_fintype_right` / `mutualInfo_le_ofReal_log_card` / `mutualInfo_eq_zero_of_ae_const` / `condMutualInfo_eq_mutualInfo_of_ae_const`) / `boolLaw` 一族 / MAC 由来の混合 `mixWeight` + `mixLaw` 一族 / `sum_measureReal_singleton_univ_eq_one` + `map_real_singleton_fiber_sum`。**BC → MAC の import 辺はこの昇格で消滅** |
| `csiszar_sum_identity_cond` / `csiszar_sum_identity` | `BroadcastChannel/OuterBoundUV/Gateway.lean` / `BroadcastChannel/ConverseGateway.lean` | 条件付き Csiszár 和恒等式 (Phase 4a の核) と無条件版 |
| `bc_degraded_converse` / `bc_input_singleletterize` | `BroadcastChannel/Converse.lean` | degraded 限定の converse (floating 形)。**degradedness を `h_deg_block` で受ける**ので 4b の橋はそのままでは効かなかった (判断ログ 11-(n))。着地は `DegradedFromCode.lean` が別配線で与えた |
| **達成側の共通形 3 本 + degraded headline** | `BroadcastChannel/Achievability/Assembly.lean` | `bc_ceil_exp_max_zero` / `bc_Ec_lt_of_clamped_rate` / **`bc_achievability_of_rate_lt`** (レートの符号制約なし、`hJlt : max R₁ 0 + R₂ < bcInfoJoint`) / `bc_achievability_of_infoJoint_ge` (`hsum` 形。**superposition 内界が実際に共有しているコアはこちら**、F-11) / `bc_achievability` (**署名・結論は逐語不変**。ただし consumer 実測 0 = クラスタの module doc を degradedness 非依存に書き替えた根拠、F-10) / `bc_degraded_infoJoint_ge` / 一文字版の degradedness `bcMarkovChain_UX_Y₁_Y₂` (ブロック版の証明骨格の雛形) |
| **superposition 内界 2 領域 (S0–S2 + more capable)** | `BroadcastChannel/Superposition/Region.lean` | `bcInfo₁_nonneg` / `@[entry_point]` `bc_lessNoisy_achievability` / 2 制約領域 `bcSuperpositionRegionNoSumRate` + `_isClosed` + `@[entry_point]` `_subset_capacity` (仮説は `hW` + `hln` のみ) / 3 制約領域 `bcSuperpositionRegionSumRate` + `_isClosed` + `@[entry_point]` `_subset_capacity` (**クラス仮説を要求しない**、`hW` のみ)。G-2 で誤称を解消し姉妹 2 領域を同居させた |
| **S3 = 情報量スロットの同定 3 本** | 同上 `### The three informations as (conditional) mutual informations` | `bcInfo₂_eq_mutualInfo_toReal` (`= I(U;Y₂).toReal`) / `bcInfoJoint_eq_mutualInfo_toReal` (`= I((U,X);Y₁).toReal`) / `bcInfo₁_eq_condMutualInfo_toReal` (`= I(X;Y₁∣U).toReal`)。`U` は `Type*` 総称 ⟹ **more capable でも再利用可**。型クラス前提は逐語 `[Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]` + `[IsProbabilityMeasure pU]` / `[IsMarkovKernel K]` / `[IsMarkovKernel W]` |
| **S6 = 時分割の補助への吸収** | `BroadcastChannel/Superposition/TimeShare.lean` | 到達点 `exists_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw` — 外界の 3 不等式 (`h₁` / `h₂` / `hsum`) を満たす点から達成側の対 `(pU, K)` を**実際に構成して**返す。G-4 でクラス free 変種 `exists_bcInfo_ge_sumRate_of_isUVChannelLaw` (+ `_of_tagged`) の系に畳み、両者が同居する。混合側 `uvTimeShareLaw` (+ `_eq` / `_isUVChannelLaw`) と `uvMixKernel_ae_tag` は **`lam ≤ 1` を要求しない** (`⊓ 1` clamp で無条件)。**一般混合 `uvMixLaw` 一族と一般スロット境界 2 本 `mul_uvInfo₂_le_uvInfo₂_uvMixLaw` / `mul_condMutualInfo_le_condMutualInfo_uvMixLaw` はこのファイルに集約済** (F-22 + F-24)。`uvTagConst` は `condMutualInfo_uvTagConst` が statement で名指すので残置し、`uvCollapse` 経由で `uvTagFalse` の特殊化として定義。cloud 側 `uvCloudLaw` / `uvSatelliteKernel` + スロット同定 3 本 `bcInfo₂_uvCloudLaw` / `bcInfo₁_uvCloudLaw` / `bcInfoJoint_uvCloudLaw` (G-3 で総称形の系に短縮) |
| **S7 = 全支持への摂動** | `BroadcastChannel/Superposition/FullSupport.lean` | 到達点 `@[entry_point]` 2 本 = 対レベルの `exists_fullSupport_bcInfo_ge` (対 `(pU, K)` を**全支持の対**に slack `δ` 以内で置き換える) と S6 と合成済の `exists_fullSupport_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw` (クラス free 変種は `_of_isUVChannelLaw`)、加えて内界 union への着地版 `sub_mem_bcSuperpositionRegionNoSumRate_of_lessNoisy_of_isUVChannelLaw`。摂動は五つ組の世界: `uvUniformLaw` / `uvPerturbLaw` (+ `_isUVChannelLaw` / `_map_aux_input_pos`) と 2 スロットの損失評価 `mul_condMutualInfo_le_condMutualInfo_uvPerturbLaw` / `mul_uvInfo₂_sub_binEntropy_le_uvInfo₂_uvPerturbLaw` (**後者の加法ペナルティは `Real.binEntropy`** — 乗法だけの下界 `≥ (1-ε)·orig` は**偽**で在庫が数値反例を持つ。タグ変数の分だけ相互情報量が増えうるので加法項は摂動の構造そのものが要求している)。対 → 五つ組の糊は `uvLawOfInput` (F-21 で `Region.lean` へ) + `uvLawOfPair` |
| **S8 = 逆包含 + 等号 (到達点)** | `BroadcastChannel/Superposition/Assembly.lean` | `.toReal` 引き算形の裾 2 本 `uvInfo₂_toReal_sub_slack_le` / `uvInfoSum₂_toReal_sub_slack_le` → 点レベル 2 本 `sub_mem_bcSuperpositionRegionNoSumRate_of_mem_uvRegion` / `mem_…_of_mem_uvRegion` → `@[entry_point]` `bc_lessNoisy_uv_subset_superposition` (**`hW` を要求しない**) → `@[entry_point]` `bc_lessNoisy_capacity_eq_uv` と bare `bc_lessNoisy_superposition_eq_capacity` |
| **more capable の等号 (Phase 5 の到達点)** | `BroadcastChannel/Superposition/MoreCapable.lean` | 条件付き more capable `IsBCMoreCapable.condMutualInfo_le` → gateway `uvInfoSum₁_le_uvInfoJoint_of_moreCapable` / 負レート枝 `uvInfo₂_le_uvInfoJoint_of_moreCapable` → 第 3 スロットの混合 `mul_uvInfoJoint_le_uvInfoJoint_uvMixLaw` / 摂動 `_uvPerturbLaw` → S7 変種 `exists_fullSupport_bcInfo_ge_sumRate_of_isUVChannelLaw` / `exists_fullSupport_bcInfo_ge_sumRate` → 点レベル `sub_mem_bcSuperpositionRegionSumRate_of_mem_uvRegion` / `mem_…_of_mem_uvRegion` → `@[entry_point]` `bc_moreCapable_uv_subset_superposition` / `bc_moreCapable_capacity_eq_uv` / **`bc_degraded_capacity_eq_uv`** (degraded の等号。`hdeg.isBCLessNoisy.isBCMoreCapable` を挟むだけの 6 行) と bare `bc_moreCapable_superposition_eq_capacity` |
| **内界の Marton union** | `BroadcastChannel/MartonUnion.lean` | `bcAuxAlphabet` (`= ULift.{u} (Fin (k+1))`) / `martonRegionUnion` / `martonRegionUnionFullSupport` (F-6 で `FS` 略記を展開) + `@[entry_point]` `martonRegionUnion_subset_uv` (明示仮説ゼロ) / `martonRegionUnionFullSupport_subset_union`。**P4/P5** = 四角形の形 `martonRegion_isLowerSet` / `_convex` / `_nonempty` と union 版 `martonRegionUnion_isLowerSet` / `_nonempty`。**P6** = 付け替え不変性 `martonJointDistribution_map_relabel` → `martonInfo₁/₂/V₁V₂_map_relabel` → `martonRegion_map_relabel` → `bcAuxMeasurableEquiv` + `@[entry_point]` `martonRegion_subset_union` (**任意 universe の四角形を union が吸収する**)。**superposition 路の補助アルファベットとしても再利用中** — `uvQuantizeLaw ν m` の第 1 成分は `ULift.{u} (Fin (m+1))` = `bcAuxAlphabet m` と**同じ型**なので、S8 で内界の union 添字に載せる橋は無料 |
| **P7 = 全支持の除去** | `BroadcastChannel/MartonFullSupport.lean` | 摂動核 `martonMixKernel` (+ `_apply` / instance / `_zero`) → 連続性 6 本 `martonMixJoint_real_continuous` / `_map_real_continuous` / `martonMix_entropy_continuous` / `martonInfo₁/₂/V₁V₂_mix_continuous` → `@[entry_point]` 2 本 **`marton_region_subset_capacity_of_channel_fullSupport`** (明示仮説は `hW : ∀ a b, 0 < (W a).real {b}` **のみ** — 補助側の `hpV` / `hK` を一様測度への摂動 + 3 情報量の連続性で除去) / **`martonRegionUnion_subset_capacity`** (内界 union の包含から全支持制限を外した版 = P7 の実り。B-5 で旧 FS 版の包含は削除)。**配置はトップ直下** (理由は §Phase 2) |
| `marton_achievability` / `InMartonRegion` | `BroadcastChannel/Marton/Achievability.lean` / `Marton/Basic.lean` | 一般 BC 内界 (EGK Thm 8.3、private message のみ、**共通補助 `U₀` なし**) と 3 不等式バンドル |
| **内外の橋 (S1–S6、全段 proof done)** | `BroadcastChannel/OuterBoundUV/MartonBridge.lean` | `martonJointDistribution_isUVChannelLaw` → `martonAuxSwapLaw` (F-6) → `martonUVLaw` + `_isUVChannelLaw` + 4 スロット保存 `uvInfo₁_martonUVLaw` 系 / `.toReal` 同定 3 本 / 和レート 4 本 (核は Markov 鎖 2 本 + 条件付き DPI。F-6 で左辺を実名 `martonInfo₁_add_martonInfo₂_sub_martonInfoV₁V₂_le_uvInfoSum₂/₁_toReal` に展開) / `marton_region_subset_uv` (`@[entry_point]`) |
| 情報量の道具 | `Shannon/CondMutualInfo.lean` / `ChannelCoding/ConverseMemorylessChainRule.lean` / `BroadcastChannel/OuterBoundUV/Gateway.lean` | 連鎖律 `mutualInfo_chain_rule` / DPI `mutualInfo_le_of_markov` / 条件付き DPI `condMutualInfo_le_of_markov_joint` / `mutualInfo_le_add_condMutualInfo` (F-b で上流移動) / 条件付き連鎖律 `condMutualInfo_chain_rule_X_2var` (S5 が実際に使った) / `condMutualInfo_le_add_condMutualInfo` (**`mutualInfo_le_add_condMutualInfo` とは別命題** — 右辺第 1 項が `I(B;C∣Z)` で、`Z` を定数にしても一致しない) |
| エントロピー / MI ↔ エントロピー形 | `Shannon/MaxEntropy/Basic.lean` / `MultipleAccess/Reconciliation.lean` / `Shannon/Entropy.lean` / **`Shannon/Pi.lean`** | `entropy_le_log_card` (家系横断の重複 2 本を `#check` 実測で同一命題と確認し MaxEntropy へ集約) / `mutualInfo_toReal_eq_entropy_form` / `condMutualInfo_eq_condEntropy_sub_condEntropy` / `entropy_pair_eq_entropy_add_condEntropy` / **`entropy_measurableEquiv_comp`** (平坦↔入れ子の再ラベル、判断ログ 16) |
| MAC の先例 | `MultipleAccess/TimeSharing.lean` / `TimeSharingConverse/{Bridge,Assembly}.lean` / `Reconciliation.lean` | 操作的述語 → closure で集合化 / 符号→ambient 橋の雛形 / 内外を同じ言語に揃える先例 / 全支持仮説を落とす完全な先例 `mac_pentagon_subset_capacityRegion_allprob`。**退化被覆と平均化は雛形にならない** (判断ログ 11-(f)) |

**存在しないもの** (項目記号は凍結): (a) 逆包含 / (b) 条件付き more capable / (d) `IsBCDegraded W`
から `h_deg_block` を出す `bcConverse_degradedBlock` は**すべて入った** (§在庫)。(e) semi-deterministic
用の 2 本は **L-BCO7 で等号を述べない判断なので目標が要求しない**。⟹ **残りゼロ**。**Mathlib 側の穴も
全 leg でゼロ**。旧 (a)「`bcOuterRegionUV ⊆ martonRegionUnionFullSupport`」は**偽** (判断ログ 18、
[`bc-facts.md`](bc-facts.md))。

## ゴール / Approach

**「まず外界」は半分正しい。その前に主語が要る。**

Approach は **「主語 → 安い外界で挟み込みの骨格 → 本命の外界 → 一致クラスの拡張」** の 4 段。
外界の重い仕事の前に Phase 1 で `bcCapacityRegion W : Set (ℝ × ℝ)` を定義し、Phase 3 の緩い外界で
**一度挟み込みを完成させてしまう**。以後の外界の改良はすべて「同じ挟み込みの右辺を狭める」差分
作業になり、1 本ごとに独立して価値が出る。この順序は Phase 1/3/4b の実績で正当化された。

**Phase 4 を 4a / 4b に割る**、というのが外界側の主判断。情報量レベル (4a、難所は Csiszár 和恒等式
の適用形、ambient を与えられたものとして受ける floating 形) と操作的レベル (4b、難所は符号から
ambient を構成する橋と n 文字平均の単一文字化) で難所が別物だから。Phase 3 がこの分割を要求しなかった
のは Wolfowitz strong converse の対偶で **ambient の構成を丸ごと迂回できた**から。

**内界側は「1 本」ではなく「クラスごとに選ぶ」** (経路変更後の主判断、判断ログ 18)。in-project の
内界は Marton union (一般 BC 向け・共通補助 `U₀` なし) と superposition (cloud + satellite) の 2 本
で、**前者は劣化 BSC 対ですら容量領域より真に小さい**ので等号を狙うクラスでは後者を使う。

## Phase 詳細

### Phase 1 / 3 / 4a ✅ (完了、1 行圧縮)

- **Phase 1** 主語を作る `fd39ad95` `deb930a7` — `BCAchievable` / `bcCapacityRegion := closure {…}` /
  `martonRegion` + `marton_region_subset_capacity`。proof-log: no
- **Phase 3** 協調外界 `e9222d0a` `b9ba272a` — BC 符号を 3 通りに還元して `bcOuterRegionCoop` +
  `bc_capacity_subset_coop`。**これで (緩い外界ながら) 挟み込みが完成**。proof-log: no
- **Phase 4a** UV 単一文字化 `5bf64adf`…`54705cb3` — 補助変数を `uvAux` 1 本に統一し identification が
  2 通りの instantiation に縮んだ。核は新規自作 `csiszar_sum_identity_cond`。proof-log: no

### Phase 2 — 補助変数についての union ✅ 完遂

M0 在庫は [`bc-phase2-union-inventory.md`](bc-phase2-union-inventory.md) (Mathlib の壁 0 件)。
最小完遂 P1–P3 ✅ (`ce8e9d0b` 在庫 / `fcdafaf5` 実装 / `b1837901` style) で
`BroadcastChannel/MartonUnion.lean` を新設し、補助の型 `k₁ k₂` と分布 `pV` / `K` についての union を
`closure` で取った (定義は §在庫 が SoT)。設計の 3 点は**機械確認済**なので蒸し返さないこと:
(a) `Fin (k+1)` であって `Fin k` でない / (b) `ULift.{u}` が要る (`IsBCLessNoisy` の `Type u` 量化) /
(c) `closure` は外側 (比較先が閉集合)。⚠ **正直な限界 (実際に発火した)**: `martonRegionUnion` は
共通補助 `U₀` を持たないので**劣化 BSC 対で `martonRegionUnionFullSupport ⊊ bcCapacityRegion`**
(判断ログ 18)。

**拡張 P4–P7 ✅ 完遂 — いずれも等号の前提ではなく、API の完全性と L-BCO2 の完答のため**:

- [x] **P4** 非空性 / 下方集合性 ✅ / [x] **P5** 凸性 ✅ (`64a2d6ab` `d0c02420`) — 四角形と union の
      両段
- [x] **P6** 補助アルファベットの付け替え不変性 ✅ (同 commit) — **L-BCO2 が「答えた」に到達**
- [x] **P7** 全支持の除去 ✅ (`fd41037e` 実装 / `813d1cfd` style / `93a3a6fb` 後片付け) — 新規
      `MartonFullSupport.lean`。在庫 §9-2 の見積りを上振れした (判断ログ 23)

**配置はトップ直下** (`MartonUnion.lean` / `MartonFullSupport.lean` とも)。⚠ **これは外部の style 監査
から繰り返し再提案される判断**なので機械確認の結論を残す: `Marton/` へ移すと
`OuterBoundUV/Assembly.lean` → `Operational.lean` → `Marton.Achievability` の既存依存と
`MartonUnion.lean` の `OuterBoundUV.MartonBridge` import が**双方向のディレクトリ依存**になり
`module-structure.md` §5 違反。フラットクラスタ解消 (同 §原則 1) より §5 が優先する。

**時分割 / 凸包は要らない** (在庫 §6 が実測で決着): union は非凸だが相手側 `bcOuterRegionUV` も非凸
なので両辺が並ぶ。時分割変数 `Q` の補助への吸収は Marton では効かない (`I(V₁;V₂)` が `H(Q)` だけ
増える) が、**superposition の 2 制約領域では効いた** (S6 ✅)。proof-log: no。

### Phase 4b — UV 外界の集合化 + 操作的包含 ✅ CLOSED

`6ddb1a48` / `bfdd55e1` `c768cc00` (M0 在庫
[`bc-uv-operational-inventory.md`](bc-uv-operational-inventory.md))。headline
`bc_capacity_subset_uv : bcCapacityRegion W ⊆ bcOuterRegionUV W` (`@[entry_point]`) を**全平面版**で
達成 — 明示仮説は `W` と `[IsMarkovKernel W]` のみ。**領域定義の確定形**:

```
bcOuterRegionUV W = closure (⋃ (ν : ProbabilityMeasure (ℕ × ℕ × α × β₁ × β₂))
                               (_ : IsUVChannelLaw W ↑ν), uvRegion ↑ν)
uvRegion ν = {p | InBCOuterRegionUV p.1 p.2 (uvInfo₁ ν).toReal (uvInfo₂ ν).toReal
                    (uvInfoSum₂ ν).toReal (uvInfoSum₁ ν).toReal}
```

closure は不可避 (半平面の交差の union は閉じない) だが、それが `bcOuterRegionUV_isClosed` を無料にする。
**第一象限制約なし** + **下方集合**の 2 点が S8-b のコストを決めた (退化被覆が約 15 行。MAC は約 420 行)。
`uvInfoSum₁/₂` の**下付き数字は受信機番号ではなく「先頭に来る corner 項の選択」** (両方とも `R₁ + R₂`
の上界)。**L-BCO4/5/6 不発動**。proof-log: **yes** (`docs/proof-logs/proof-log-bc-uv-operational.md`)。

### Phase 5 — 一致するクラスを広げる ✅ 完遂

degraded の一般化を、内界と Phase 4b の外界の組で回収した。**内界は Marton union ではなく
superposition** (経路変更、判断ログ 18)。到達点の署名は §在庫 が SoT。

- **定義段 ✅** `2c938fe0`…`42ac21e7` (M0 在庫
  [`bc-phase5-class-inventory.md`](bc-phase5-class-inventory.md)) — `martonRegion` から
  `0 ≤ p.1 ∧ 0 ≤ p.2` を除去 (**これをやるまで等号はどのクラスでも述べられなかった**) + `Classes.lean`
  の 3 クラス + 包含鎖 `degraded ⊆ less noisy ⊆ more capable`
- **内外の橋 S1–S6 ✅** `6b0c1ea1`…`0186b708` (M0 在庫
  [`bc-inner-outer-bridge-inventory.md`](bc-inner-outer-bridge-inventory.md)) — Marton 結合法を外界の
  `ℕ` 添字に載せ順包含 `marton_region_subset_uv` (`@[entry_point]`) まで運んだ。**`hpV` / `hK` / `hW` を
  1 本も要求しない** (判断ログ 15) ので経路変更後もそのまま生きている
- **less noisy の等号 ✅** S0–S8 全段 proof done (`06817339`…`558b3fca`、M0 在庫
  [`bc-lessnoisy-equality-inventory.md`](bc-lessnoisy-equality-inventory.md)、段ごとは
  `bc-s{5,6,7,8}-*-inventory.md`)。**plan が次手としていた
  `bcOuterRegionUV ⊆ martonRegionUnionFullSupport` は偽**と判定され (判断ログ 18) 内界を差し替えた結果。
  **`hW` の要る場所は逆包含ではなく内界を符号に落とす段だけ**で、順包含 `bc_capacity_subset_uv`
  は無条件。経緯は [proof-log](../proof-logs/proof-log-bc-lessnoisy-equality.md)
- **more capable の等号 ✅** `4a01dff8`…`594887a4` (M0 在庫 `6527722b`
  [`bc-morecapable-equality-inventory.md`](bc-morecapable-equality-inventory.md)、実測は在庫の帯の中、
  壁 0 / 穴 0 / 設計バックトラック 0)。`IsBCLessNoisy.isBCMoreCapable` 経由で `bc_lessNoisy_*` を
  **包含する** (畳み直しは意図的に未実施 = §後続作業 G-1)。設計の要は 2 点 — **第 3 制約を
  `max p.1 0 + p.2 ≤ bcInfoJoint`** と書いて達成側の入口 `bc_achievability_of_rate_lt` の `hJlt` に
  逐語で合わせたことが**内界の達成可能性からクラス仮説を落とした** (素直な形にすると負レート枝で
  クラス仮説が達成側に漏れる) / 核は**条件付き版** `IsBCMoreCapable.condMutualInfo_le` で、これが
  **less noisy の逆包含が捨てていた外界の 4 本目 `sumBound₁` を第 3 制約の担い手に変えた**
  (負レート枝が要求する `uvInfo₂ ν ≤ I(X;Y₁)` は plan にも S8 在庫にも無かった obligation、
  判断ログ 24-(i))
- **degraded との接続 ✅** `bf49a91d`…`86b90af1` (M0 在庫 `b18526c1`
  [`bc-degraded-connection-inventory.md`](bc-degraded-connection-inventory.md))。**価値は等号ではなく
  古典形 converse (Cover–Thomas Thm 15.6.2) の操作的着地** — 領域レベルの等号
  `bc_degraded_capacity_eq_uv` は more capable の 6 行の系にすぎない。本体は、`bc_degraded_converse` が
  degradedness と memorylessness を構造前提 (`h_deg_block` / `h_memo`) で受け `Converse.lean` の
  docstring が "not load-bearing" と**散文で主張していた**ものを、`bc_degraded_converse_from_code` が
  `bcConverseAmbient c W` で実際に discharge して**機械検証に変えた**点 (残る明示仮説は
  `IsBCDegraded W` と 2 本のメッセージ数だけ)。**L-BCO10 不発動**
- **semi-deterministic 📋 = 新規作業なし** — 定義は入ったが**内界の定理が適用できない** (全支持仮説を
  定義上必ず破る、判断ログ 13) ⟹ 等号は **L-BCO7** で defer し外界側だけで止める。判定対象は
  `bc_achievability_of_rate_lt` の `hpU` / `hK` / `hW` の 3 本

proof-log: 個別 leg は no、族としての 1 本は ✅ 完了 (`3d680d3e`、
[`proof-log-bc-lessnoisy-equality.md`](../proof-logs/proof-log-bc-lessnoisy-equality.md))。
**more capable の leg は yes**、**degraded 接続は no** (要点は上記と判断ログ 11-(n)/(q) · 23 · 29)。

## 後続作業 (Phase 5 の前提ではない)

style / honesty ゲートが提起して当該 leg では見送った項目。完了したものは 1 行 + commit に圧縮して
残す (項目番号は他文書が参照するので付け替えない)。

**完了 (1 行 + commit に圧縮)**:

- **A** `Assembly.lean` の二段分割 (`210b7558`…`3af79fea`) / **F-a** `isMarkovChain_map_comp` を
  `CodeToAmbient.lean` へ上流移動 (`102d514a` `28aafa87`) / **F-12** 四つ組法を
  `IsUVChannelLaw.map_auxiliary_input_output` へリネーム (`c3508204`) / **F-5** README 定理表登録
  (`b545cbd7`) / **F-19** `Superposition/` 昇格 (`4ea35cc0`) / **F-21** `uvConstLaw` を
  `uvLawOfInput` の dirac 特殊化に畳む (`bf8519c6`) / **F-22** S6 の分岐クラスタを `uvMixLaw` に畳む
  (`d5a30401`) / **F-c** `ℝ≥0∞` 引き算形 4 箇所を `ENNReal.toReal_le_add` に置換 (`114d7654`、
  style PASS `d0ac3aed`) / **F-28** `uvInfoJoint` の def 化 + ベタ書き置換 (`bb40c820`) /
  **F-15 の汎用 2 本** `condMutualInfo_congr_measure` → `Shannon/CondMutualInfo.lean`、
  `mutualInfo_congr_pair` → `Shannon/MutualInfo.lean` (`730844a1`)
- **B-1 / B-5** 死んだ宣言 2 本 (bc_uv_rate_extract / martonRegionUnionFS_subset_capacity) を削除 /
  **B-2** `*_point_mem` 5 本を `_of_<仮説>` 軸へ改名 / **F-1** bcJointDistribution_id_eq →
  `bcJointDistribution_id_eq_map_compProd` / **F-6** 改名束 (auxNatIndex → `natIndex` /
  martonSwapLaw → `martonAuxSwapLaw` / `FS` → `FullSupport` 3 本 / martonInfoSum の実名展開 2 本) /
  **F-25** BC 族外の `ℝ≥0∞` イディオム 2 箇所 (`aad88f5d` `715605b7`)
- **F-6 の残り** `natIndex` は `Encodable.encode` に**寄せず据え置き**、設計理由を docstring に明記
  (`9d16a21e`)
- **F-29** `IsBCDegraded` を `Achievability/Setup.lean` → `Basic.lean` へ移設 (`19d7f6ab` `6630a5ee`)
- **F-15 / F-24** 汎用 11 本を新規 `Shannon/MutualInfoFiniteRange.lean` + `Shannon/BoolLaw.lean` へ
  昇格、F-24 の一般スロット境界 2 本を `TimeShare.lean` へ集約 (`27c909ca` `61971e9b`)。**軸の逆側**
  = MAC namespace の汎用 API を新規 `Probability/Mixture.lean` + `Probability/SingletonMass.lean` へ
  昇格し `mac` 接頭辞を除去 ⟹ **P7 が足した BC → MAC の import 辺が消滅** (`08cfde86` `cacc59d6`)
- **D-1 / G-3 / G-4 / F-24 残余** 4 件の重複を既存一般形の系へ畳む (純減 102 行、`083aceef`
  `434f16fd`)
- **G-2** 誤称 bcSuperpositionRegionFullSupport → `bcSuperpositionRegionNoSumRate`、姉妹の SumRate
  領域を `Superposition/Region.lean` へ集約 (`2ed67320` `371dce85`)
- **E-1** `CondMutualInfoMixture.lean` を分割し再符号化不変性を新規
  `Shannon/MutualInfoReencoding.lean` へ (`abbf8e58` `43cd2d0c`)
- **F-10 / F-11 / F-d / C-3** `Achievability/` クラスタ 4 本の module doc タイトルを degradedness
  非依存の実態へ同期 (**consumer 実測で確定**: 総称形の consumer 3 箇所に対し degraded headline
  `bc_achievability` は 0) / `bc_lessNoisy_achievability` の docstring が名指す共有コアを
  `bc_achievability_of_infoJoint_ge` に是正 / `MartonBridge.lean` の兄弟 3 本を private に揃え
  Main statements から除去 / `show` → `change` (`6a0c68ff` `4bc00e36`)
- **F-3 / F-4 / F-13 / F-b** 語彙橋 2 本を private 化 / `…_of_one_lt_card` 追加 /
  `isMarkovChain_map_comp` の引数順を兄弟 `condMutualInfo_map_comp'` に合わせ (呼び出し 3 箇所追随) /
  `mutualInfo_le_add_condMutualInfo` を `Shannon/CondMutualInfo.lean` へ上流移動 (`8cac522b`
  `054f3994` `be0750b8`)。⚠ **F-b が「条件付き版が Gateway に既存」としていたのは誤り** —
  `condMutualInfo_le_add_condMutualInfo` は右辺第 1 項が `I(B;C∣Z)` で**別命題**、`Z` を定数にしても
  一致しない (判断ログ 24 の ⊕)
- **家系横断** `entropy_le_log_card` の重複 2 本 (`SlepianWolf/Basic.lean` / `MaxEntropy/Basic.lean`)
  が `#check` 実測で**型クラス前提まで完全同一命題**と判明 → SlepianWolf 側を削除して MaxEntropy へ
  集約、call site 9 箇所を統一、`docs/readme-theorems.txt` の曖昧性回避子を除去 (`b5c55683`
  `939e3550`)
- **B-2 の姉妹追随 + MAC 命名衝突** MAC 側 3 本を
  `mac_converse_rate₁/₂_mul_one_sub_errorProb_mem_of_ceil_exp_le` 系へ改名 (`6de04dd9` `12109990`) /
  同一 namespace で `axis1` が正反対を指していた衝突を、下付き = 生きている座標に統一して解消
  (`mac_rate₁/₂_achievable` / `mac_timesharing_converse_rate₁/₂`、`d832baef` `9081cef4`。判断ログ 25 の ⊕)

### B. 命名 (残り 2 件、いずれも優先度低)

3. `uvAux_pad_mutualInfo_prod_eq` (`Bridge.lean`) の `prod` が何の直積か読めない
4. `_cond` の位置が Mathlib 順と逆な `condMutualInfo_eq_of_leftInverse_cond`

### C. 数学的な締めどころ / その他

1. **`bcConverseFanoSlack₁_le` が 2 bit 捨てている** (`Real.log (M₁-1) ≤ Real.log M₁` への緩和) —
   converse の結論には効かないが、レートの残差を詰めたくなったときの最初の締めどころ
2. `bcOuterRegionUV ⊆ bcOuterRegionCoop` を示せれば「UV は協調外界より狭い」が機械可読になる (**任意**)
4. **section 再配置による逐語コピーの完全畳み込み (残 ~30 行)** — 現配置では不可能
   (`bcUVJointDistribution` は `uvAuxPad` に依存し `uvAuxPad` は `bc_uv_converse_from_code` より後ろ)
5. **規約どうしが同じケースで逆方向に引く件 (本 plan の範囲外・記録のみ)** → **F-17 / G-5**

### D. 汎用補題の置換統合 (未着手)

2. `mutualInfo_eq_of_leftInverse` (`Shannon/MutualInfoReencoding.lean`) は `MIChainRule.lean` の
   `mutualInfo_map_left_measurableEquiv` を subsume する。数学は増えず consumer 書き換えだけが
   コストなので着手判断は波及の大きさで決まる (`dep_consumers.sh` で引き直すこと)。**import 面の
   判断が先**: consumer に `MIChainRule.lean` 自身が含まれ、置換すると**chain-rule ハブに
   KL-integral 依存が入る**。E-1 の分割後、この関係は `MutualInfoReencoding.lean` の module doc に
   明記されている

### E. 分割 A が新たに立てた flag (優先度低)

2. **`open scoped BigOperators` が tree 全体で死んでいる** — tree 一括 sweep の別 leg で**範囲外**

### F. Phase 5 / Phase 2 / S0–S8 が新たに立てた flag

9. **`docs/rules/lean-style.md` の「演算子は行末に置いて改行する」が repo 実態と矛盾** (**本 plan の
   範囲外・記録のみ**) — 複数行シグネチャの**関係記号**には当てはまっていない (継続行を関係記号で
   始める行は tree 全体で数千行規模)。起票先は `docs/rules/` 側
14. **`unusedDecidableInType` warning (family 一括の別 leg)** — 実測で tree 全体 27 ファイル /
    292 宣言、`Superposition/Region.lean` はうち 6 件。⚠ **`omit` では消せない**: `[DecidableEq U]` は
    各定理が自前で束縛しているので、解消するなら 5 宣言の**署名変更**になる ⟹ BC 単独では取らない
17. **§C-5 の規約衝突は機構が特定済** (本 plan の範囲外・記録のみ) — 原因は**規約文が決着に追随して
    いないこと**: 実効ルールは「**docstring 必須は `@[entry_point]` headline**、`@[entry_point]` の
    無い Main statements エントリは name-adequacy で bare」なのに `docs/rules/docstrings.md` item 1 の
    括弧が旧文言のまま。**恒久解は item 1 の括弧を `@[entry_point]` のみに直すこと** (起票先は
    `docs/rules/` 側)
20. **内ループの `lake env lean` は一部の linter に盲目 (検証の穴)** — S7 で実測が裏付けた ⟹ family の
    既定手を 2 段にする: **実装 leg の検証バーに `lake build <module>` を含める** + **在庫 leg の
    probe 段階から linter 条件を有効にする**
23. **`isUVChannelLaw_iff` (`OuterBoundUV/Region.lean`) の右辺が `uvLawOfInput` の本体を逐語で
    書き下している** — def を名指す形へ書き換えれば重複は消えるが**これは statement の変更**で全
    consumer が再エラボレートされる ⟹ `scripts/dep_consumers.sh …isUVChannelLaw_iff` から始める
    独立 leg。⚠ **着手前に判断ログ 9 を読むこと**: この `iff` は「外界が平面全体に退化しない」ことを
    与えている特徴づけそのものなので、触る leg は**まずその性質が壊れないかを点検する**
26. **同期 leg が手で数えた数値は、行数も個数も較正基準に引かない (⚠ 記録のみ — 在庫は編集しない)** —
    3 件が同機構で外れた。徴候は **同じ 1 つの数値が逆向きの 2 主張 (下振れ無し / 上振れ無し) を
    支えている**こと (伝播したのは測定値ではなく「的中した」という評価語) ⟹ **次の在庫 leg は
    `bc-s6-timesharing-inventory.md` / `bc-s7-fullsupport-inventory.md` のその 2 文のどちらも引かない**。
    ⟹ **行数・宣言数・置換箇所数はすべて re-derive 側**で、行数は `git show <commit>:<path> | wc -l`、
    個数は**名前ではなく結論形・接尾辞で再検索**する。経緯は proof-log §8 2 本
    ([lessnoisy](../proof-logs/proof-log-bc-lessnoisy-equality.md) /
    [morecapable](../proof-logs/proof-log-bc-morecapable-equality.md))
27. **行数の機械照合を `scripts/plan_lint.ts` に足す (本 plan の範囲外・記録のみ)** — commit hash と
    併記された**ファイル単位**の行数は `git show <commit>:<path> | wc -l` で機械照合できるのに、
    現行 linter は decl / `file:line` / wall slug しか突き合わせていない。**起票先は `scripts/` 側で
    BC の leg は実装しない** (F-9 / F-17 と同じ扱い)。⚠ 射程はファイル単位まで — **宣言クラスタ単位**の
    数値は数え方が規約化されておらず機械照合できない

### G. more capable の等号 leg が新たに立てた flag

1. **`bc_lessNoisy_*` を `bc_moreCapable_*` の系に畳む** — `IsBCLessNoisy.isBCMoreCapable` があるので
   2 行で出る。**本 leg では意図的にやらなかった** (S5–S8 の機械は 3 制約版が再利用するので消せず、
   書き換えは純 churn)。着手するなら独立 leg
5. **`docs/rules/docstrings.md` item 1 と `scripts/lean_doc_lint.ts` の衝突を起票した** (F-17 / §C-5
   と同じ機構、**恒久解の担当は別家系**)。安い運用解は「**docstring を付けたい headline には
   `@[entry_point]` を付ける**」の明文化。⚠ **BC 家系の外に効くので本 plan では実作業をしない**
6. **ファイル移動 / 昇格を伴う leg のチェックリストに `gen_readme_table.ts --write` を入れる** —
   F-19 でパスが変わったまま表が古く `--check` が FAIL していた。生成表は「移動しても自己修復
   する」設計だが**`--write` を回して初めて効く**

## 未解決本体との距離 (正直な見積り)

「Marton 内界 = 一般 BC の容量領域か」は **open**。数学が存在しないので形式化できない。得られるのは
(a) 内界・外界・容量領域が同一言語で並び**ギャップが機械可読な形で固定される**、(b) 特定の BC で内外が
分離するかを検証する基盤 (**既に 1 度使われた**、判断ログ 18)、(c) 一致が既知の特殊クラスで等号が
閉じる (Phase 5) の 3 点。期待値は「足場 + 教材価値」に置く。

## 設計上の未決事項

1. **補助変数 union の射程** (Phase 2) — **濃度固定で止める形で決着**。情報理論側の Carathéodory
   (支持補題) は書かない (Fenchel–Eggleston が Mathlib 不在ゆえ自作行数が跳ねる)。P7 を取るかの
   判断は**取る側で決着**し完遂した (§Phase 2)
3. **`martonInfo*` を `ℝ≥0∞` 版へ pivot するか** — **less noisy の等号からは外れた**。superposition
   路では `I(V₁;V₂)` (補助 × 補助) が現れず 4 スロットすべてが出力との情報量なので `.toReal` の
   危険が構造的に発火しない ⟹ **Marton union の API を完成させたくなったときだけの判断**。
   `uvRegion` 側の同じ問いは決着済 (有限アルファベットでは無関係)

## 撤退ライン (frozen slug)

| slug | 発動条件 | 退避先 |
|---|---|---|
| **L-BCO1** | Phase 4 の補助変数 identification が閉じない | **不発動** (Phase 4a) |
| **L-BCO2** | Phase 2 の型量化 union が universe 問題で詰む | 濃度固定版で止め union は取らない。**不発動** — 問題は union の定義側ではなく**消費側** (`IsBCLessNoisy` が `U : Type u` を量化) にあり `bcAuxAlphabet = ULift.{u} (Fin (k+1))` が **0 行で吸収**した。**P6 (付け替え不変性) が閉じたら「答えた」になる** — その条件は満たされた (`64a2d6ab`、`martonRegion_subset_union` が任意 universe の四角形を union に吸収する) ⟹ **「答えた」に到達、retire** |
| **L-BCO3** | (凍結文言) Phase 5 の等号が Phase 4 の外界の形と噛み合わない。⚠ **最後の判定対象だった more capable が閉じ retire** (L-BCO9 と同じ扱い。slug は凍結なので文言は残す) | **less noisy でも more capable でも不発動**。**発動条件の文言は実態とずれていた** — 噛み合わなさの本体は外界の形ではなく**内界の形**だった (符号制約 = `2c938fe0` で解消 / 内界の選択 = 判断ログ 18 で superposition へ / 全支持仮説 = L-BCO7)。用意していた退避先 (逆包含を署名を保ったまま `sorry` + `@residual(plan:bc-morecapable-converse)`) は使わなかった。**`IsMoreCapableTight` のような「等号が成り立つ」を束ねる述語は作らない**という禁止 (L-BCO9 由来) だけが後続クラスへ引き継がれる |
| **L-BCO4** | Phase 4b の符号→ambient 橋または単一文字還元が閉じない | **不発動のまま Phase 4b が完遂** |
| **L-BCO5** | S5 の補助変数の型統一が `mutualInfo_chain_rule` 経由でも閉じない | **不発動** (在庫の攻略路がそのまま効いた)。退避先だった `bcOuterRegionUVAt W n` + `⋂ n` 版は採らない |
| **L-BCO6** | S8-b の退化レート被覆が MAC 同様 450 行級に膨らむ | **不発動** — 全平面版で closure した (退化被覆は約 15 行) |
| **L-BCO7** | semi-deterministic の等号を狙う段で、内界の達成側の全支持仮説が外せない (判断ログ 13) | **semi-deterministic はクラス定義 + 外界側だけで止め、等号は述べない**。外界 (`bc_capacity_subset_uv` の特殊化) は `hW` を要求しないので単独で成立する。退避の出口は `sorry` + `@residual(plan:bc-semideterministic-fullsupport)`。**`IsSemiDeterministicAchievable` のような述語に核を束ねる形は取らない**。**判定対象は経路変更で移った** — 旧: `marton_achievability` の `hW` / 新: `bc_achievability_of_rate_lt` の `hpU` / `hK` / `hW`。橋 S1–S6 は明示仮説が `pV` / `K` / `W` と型クラスだけで全支持仮説を 1 本も要求しない (署名走査で実測) ので本ラインの外 |
| **L-BCO8** | (**⚠ 無効化**。逆包含 `bcOuterRegionUV ⊆ martonRegionUnionFullSupport` が**偽**と判定され枠組みごと失効、判断ログ 18) | **⚠ 使用禁止** — 旧退避先「`sorry` で署名を保つ」は偽の命題を署名に残すことになり取れない (CLAUDE.md 検証の誠実性)。後継は **L-BCO9** |
| **L-BCO9** | (凍結文言) less noisy の等号で **S6 (時分割の補助への吸収) が閉じない**。⚠ **S5 / S6 / S7 / S8 の 4 段連続で不発動 ⟹ 判定の担い手を失い retire** (`c3508204` / `70fc424e` / `560c3399` / `3ca197cd` で proof done)。slug は凍結なので文言は残す | 逆包含 (凍結文言では bc_uv_subset_superposition、**現行名は `bc_lessNoisy_uv_subset_superposition`** — 判断ログ 25 で改名) を **署名を保ったまま** `sorry` + `@residual(plan:bc-lessnoisy-converse-quantization)` で残す予定だったが、**逆包含は無条件に閉じた**ので退避先は使われなかった。**`IsLessNoisyTight` / `IsSuperpositionOptimal` のような「等号が成り立つ」を束ねる述語は作らない**という禁止だけが後続クラスへ引き継がれる |
| **L-BCO10** | degraded 接続で `bcConverse_block_append` (pi 積 → compProd の再結合) が閉じない。在庫 `b18526c1` が提案 | **不発動** — 1 発で閉じた。退避先 (`bcConverse_degradedBlock` の署名を逐語で保ったまま body を `sorry` + `@residual(plan:bc-degraded-block-append)` にし、配線 `bc_degraded_converse_from_code` はそのまま完成させる) は使わなかった。**degradedness を `*Hypothesis` 述語に束ねて配線の仮説に足す形は取らない**という禁止だけが残る |

**active な撤退ラインは L-BCO7 のみ** (semi-deterministic。ただし等号を述べない判断が済んでいるので
新規作業は生まない)。L-BCO8 は無効化、**L-BCO2 は「答えた」に到達し、L-BCO3 / L-BCO9 / L-BCO10 は
不発動のまま retire** (いずれも履歴として残置)。

**禁止事項**: どの撤退でも「外界が成立する」「補助変数が取れる」「符号から ambient が取れる」等を
`*Hypothesis` 述語に束ねて仮説として渡す形は取らない (CLAUDE.md 検証の誠実性 tier 5)。退避は
`sorry` + `@residual` で、署名は証明したい形のまま保つ。**ただし偽と判定された命題は署名としても
残さない** (L-BCO8 の教訓) — 偽の署名に `sorry` を置くのは充填不能な `sorry` を作ることであり、
その場合は退避ではなく**目標の差し替え**が正しい手。Phase 5 で等号を述べる段では、クラス条件
(less noisy 等) を「等号が成り立つ」に近い形の述語で受け取っていないかを毎回確認する。
**撤退ラインは「どの宣言が止まるか」まで降ろして書く** — 「クラス X では内界が使えない」の粒度だと
無関係な後続 step まで巻き込んで park することになる (L-BCO7 が実際に緩んだ経緯)。

## 推奨実行順

**Phase 5 は完遂** (等号は less noisy / more capable、degraded は古典形 converse の着地まで):

```
Phase 5 定義段 ✅ → 内外の橋 S1–S6 ✅ → Phase 2 最小完遂 P1–P3 ✅ (Marton union の順包含は生きている)
S0 factor out ✅ → S1 less noisy 接続 ✅ → S2 内界の集合化 ✅ → S3 スロット同定 ✅ → S4 Markov 鎖 ✅
  → S5 量子化 ✅ → S6 時分割 ✅ → S7 全支持摂動 ✅ → S8 逆包含 + 等号 ✅
  → more capable ✅ (S3 は逐語再利用、S4 / S5 は 1 本ずつ追加、S6–S8 は変種)
  → degraded 接続 ✅ (等号は more capable の 6 行の系、本体は古典形 converse の符号への着地)
```

**後片付け (README 登録 F-5 / refactor leg F-19 + F-21 + F-22 + F-c / F-28 / F-15) と記録
(proof-log `3d680d3e`) も完了**。**Phase としての実作業は全て完了**:

| # | 作業 | 結果 |
|---|---|---|
| **1** | **proof-log** ✅ `3d680d3e` | [`proof-log-bc-lessnoisy-equality.md`](../proof-logs/proof-log-bc-lessnoisy-equality.md) |
| **2** | **more capable の等号** ✅ `4a01dff8`…`594887a4` | 在庫の帯の中 |
| **3** | **degraded との接続** ✅ `bf49a91d`…`86b90af1` | 初の下端割れ (判断ログ 23) |
| **4** | **Phase 2 の P4–P7** ✅ `64a2d6ab`…`93a3a6fb` | P7 は在庫の帯を上振れ (判断ログ 23) |
| **5** | **semi-deterministic** | **新規作業なし** — L-BCO7 で判断済 |
| **6** | **後続作業の一括消化 (9 leg relay)** ✅ `aad88f5d`…`9081cef4` | 上記「完了」欄。残るのは B-3 / B-4 / C-1 / C-2 / C-4 / D-2 / E-2 / F-14 / F-23 / G-1 |

**新しい数学を含む leg は在庫 leg から始める** (根拠は判断ログ 23。**行数見積りは数学と散文・section を
別枠で積む**)。

## 判断ログ

9. **`IsUVChannelLaw` は load-bearing hyp ではなく包含の右辺を縮める構造条件** (監査判定): union を
   無制約に取ると出力を入力にコピーする `ν` が 4 スロットを任意に大きくでき、**外界が平面全体に
   退化して `bc_capacity_subset_uv` が vacuous に真になる**。`isUVChannelLaw_iff` が「union の添字は
   補助と入力の任意の同時法をチャネルに通したもの ちょうど」を与えて反例 class ごと閉じている。
   **外界の形を触るときはこの特徴づけが壊れないかが最初のチェック点** (S4 / S5 は通過 =
   消費側でも十分に強かった)。
11. **在庫予測の外れ — 在庫ファイルは編集しないので本エントリが記録の SoT** (件数は手で数えないこと
    = F-26)。生きた教訓のみ残す (settled な個別項目は git):
    - **(f) 雛形を参照するときは「その雛形の到達目標が自分と同じ強さか」を先に確認し、却下する
      ときは「宣言」と「証明骨格」のどちらを却下したのかまで書く** — S6 の `bcUVTimeShare` は
      **宣言としては再利用不可**だったが**証明骨格は逐語で効いた**。degraded 接続でも同じ形で
      `bcMarkovChain_UX_Y₁_Y₂` (一文字版) が宣言不可・骨格可の雛形になった。
    - **(g) 前 step の到達点が次 step の入口として使えるとは限らない** — 縮小点の**加法形**は極限に
      乗らない。**乗法形**への差し替えで解決。step 境界では結論の**形**を独立に確認する。
    - **(i) import の必要性は consumer 表ではなく移動先の依存の閉包で決まる** (分割 A の 3 件 +
      F-a + F-15)。
    - **(k) 「独立」「park 可」の判定は到達目標ごとに違う** — park 判定は目標を名指して書く。
      Phase 2 は「等号の前提」だったが内界が superposition に移って前提でなくなった ⟹
      **目標側が差し替わると依存関係の宣言は失効する**。
    - **(n) 「同じ floating 形だから橋が効く」は形の一致であって仮説の一致ではない (理由を引き直した)** —
      「4b の橋の対応版が 0 hit」は事実だが、**理由の記述が浅かった**。`isMarkovChain_of_compProd_pi`
      一族が効かないのは仮説の表現が違うからだけではなく、この一族が **`W` を不透明なカーネルとして
      扱い degradedness を一切見ない**から (在庫 §Q3-2)。効いたのは達成側の一文字版
      degradedness 雛形 (`bcMarkovChain_UX_Y₁_Y₂` の証明骨格 + `isMarkovChain_of_append`)。
      ⟹ 再利用可否は結論形でも仮説の綴りでもなく、**その資産が本命の構造を見ているか**で決まる。
    - **(q) 在庫の仮称 → 実物の対応表 (在庫は編集しないので本表が唯一の対応記録)**:
      qBlock → `piBlockKernel` / degraded_singleton → `measure_singleton_eq_mul_of_append` /
      pi_unzip_eq_compProd → `pi_map_unzip_eq_compProd` / pi_map_comp_injective →
      `pi_map_comp_of_injective` / bcConverse_degBlock → `bcConverse_degradedBlock` /
      bc_converse_from_code → `bc_degraded_converse_from_code` / **bc_converse →
      `bc_degraded_converse`** (判断ログ 25) /
      ファイル名 DegradedConnection.lean → `DegradedFromCode.lean` (旧名は引退済なので裸書き)。
    - **(o) 在庫の依存の向きが 1 本ずれた (S5)** — 「`uvInfo₂` の有限性は DPI 経由でしか出ない」は
      誤りで、片側有限性 `mutualInfo_ne_top_of_fintype_right` を先に入れればチャネル法を使わず直接
      出る。**「S5-a を gateway-atom として先に切る」という順序判断は正しく、理由だけがずれていた**
      ⟹ 実装時は在庫の *順序* だけ引き継ぎ、*理由* は自分で引き直す。
13. **semi-deterministic は内界の定理と構造的に非両立 (L-BCO7 の根拠)**: 達成側の全支持仮説
    `hW : ∀ a b, 0 < (W a).real {b}` を **semi-deterministic は定義上必ず破る** (in-tree の証拠は
    `IsBCSemiDeterministic.exists_prob_real_singleton_eq_zero_of_one_lt_card`)。superposition 路でも
    全支持は要るので内界を差し替えても解消しない。⟹ 一般教訓: **「文献で容量領域が既知」と
    「in-project の内界定理が適用できる」は別** — クラスを候補に挙げる前に既存定理の regularity
    前提との両立を見る。
18. 🔄 **内界の選択はクラスごとに変わる — `martonRegionUnion` は劣化 BSC 対ですら容量領域より真に
    小さい (経路変更)**: `bcOuterRegionUV ⊆ martonRegionUnionFullSupport` は**偽** (数値と再検証
    コマンドは [`bc-facts.md`](bc-facts.md))。原因は共通補助 `U₀` の不在で、`U₀` は `martonRegion` の
    署名に **入る余地がない** ⟹ 内界を superposition に差し替え、L-BCO8 を無効化し L-BCO9 を新設した。
    ⟹ **一般教訓**: **「内界 ⊆ 容量領域」を持つことは「その内界で等号が狙える」を意味しない** —
    等号の相手として使う前に、既知の到達点がその内界に入るかを 1 度数値で当たる。
23. **plan の粗見積りは在庫 probe で必ず上書きする。ただし probe 行数は「下限」であって予測ではない
    (S7 で 6.5 倍 / S8 で約 2 倍の外れ)**: どちらも実測は**在庫の帯の中で、plan の外** ⟹ **probe を
    持たない見積りは桁で外れうる**。⚠ **「probe があれば数学の行数は当たる」も誤り** — probe →
    as-landed は S5 / S6 とも上振れで、probe が覆うのは**その probe に書いた分だけ**。S7 以降で効いた
    のは probe の存在ではなく**見積り表を「数学 (probe 実測) / 散文・section」の 2 列に割った**こと
    ⟹ **見積りは 2 枠で積み、probe 行数は下限として読む**。誤記の伝播は §後続作業 F-26 / F-27。
    ⊕ **degraded 接続 = 2 列見積り 5 leg 目にして初めて下端を割った**。主因は**主目標の結論が
    `isMarkovChain_of_append` の `h_app` と逐語一致し可測性 3 本を添えるだけで済んだ**ことで、その
    `isMarkovChain_of_append` は**同じ leg の leg A が `private` を解除して上流公開した**資産
    ⟹ 一般則: **在庫は移設前の状態で見積もるので、leg 内 / leg 間の資産移設は後続 step の見積りを
    下振れさせる**。帯の外れ方が上下どちら向きでも、原因は「見積り時点と着手時点で在庫が違う」。
    ⊕ **P7 = 見積りは「ルート」に紐づくのであって「同じ命題の別家系版」には移らない**: **新しい数学は
    Kernel 側の摂動と連続性の写しだけ**で、残りは署名の反復と section の運賃。plan は「superposition
    側の対応物 S7 があるので P7 の見積りを信じるな」と警告していたが、**S7 は模倣しなくてよかった** —
    Marton 側は全アルファベットが `Fintype` なので S7 の混合不等式ルートではなく MAC 由来の
    連続性ルートが効く。⟹ **警告の向きは正しかったが根拠がずれていた**: 移らないのは「同じ命題を
    他家系で解いた行数」であって、移るのは「同じルートを踏んだ行数」。
    S7 では**署名の高さの予測も外れた** (S6 の到達点が `ν` を存在量化して捨てるため法 → 法では
    合成できず headline は対レベル) ⟹ **step をまたぐ設計判断は「何を摂動するか」ではなく
    「前 step の到達点が何を返すか」で決まる** (11-(g) の署名版)。
24. **plan が「残るのは X だけ」と書いたら、前 step の到達点が要求する仮説を 1 本ずつ数えて
    突き合わせる** (在庫が plan の誤りを見つけたのは S6 / S7 / S8 / more capable の **4 leg 連続**)。
    誤りは 2 軸に分かれる: (i) **仮説の軸 (数え漏れ)** = S8 の擬似 Lean は S5 の裾評価 3 本しか運んで
    おらず S6/S7 の入口が要求する `h₁` の担い手が plan 上に存在しなかった / more capable では負レート枝の
    `uvInfo₂ ν ≤ I(X;Y₁)` が plan にも S8 在庫にも無かった ⟹ **到達点の署名を数えるのは在庫 leg の
    最初の 5 分の作業で、plan の粗見積りより安い**。(ii) **資産の軸** = plan は「既存の受け皿
    `InBCCapacityRegion` では受けきれず新 structure が要る」と書いたが、内界はその structure を
    **そもそも消費していなかった** ⟹ **plan が「既存の X では受けきれない」と書いたら、着手前に
    X の消費者を `dep_consumers.sh` で確かめる**。(ii) は**確かめずに書いた否定**で、CLAUDE.md
    「A dismissed asset must be dismissed by the compiler」の plan 版 — 数え漏れと違い、下流に
    **存在しない作業を生む**。
    ⊕ **同じ機構が肯定形でも出た (F-b)**: plan は移設対象の「条件付き版が既に別ファイルに public で
    ある」と書いたが、実物 `condMutualInfo_le_add_condMutualInfo` は右辺第 1 項が `I(B;C∣Z)` の
    **別命題**で、`Z` を定数化しても一致しない。⟹ **plan が「同等物が既にある」と書いたときも、
    型を並べて突き合わせるまで採らない** — 否定形は存在しない作業を生み、肯定形は**必要な作業を
    消す** (こちらのほうが検出が遅れる)。
25. **名前が仮説を語らないと、隣の無条件定理に引きずられて誤読される**: 逆包含は一般 BC では
    **偽**で `hln` が本質的なのに、旧名 bc_uv_subset_superposition (引退済) は仮説を 1 つも語らず、隣に
    **無条件**の `bc_capacity_subset_uv` が並んでいた。style ゲートが検出し consumer 0 の段階で改名
    (more capable では逆方向 = **制約の本数 `3` という statement に現れないメタデータが名前に入って
    いた**のを `bcSuperpositionRegionSumRate` へ改名) ⟹ 一般則: **クラス限定の定理は名前にクラスを
    入れ、statement に現れない量は名前から出す** — どちらも consumer が付く前が唯一の安い時機。
    ⊕ **degraded 接続では対象が新規宣言ではなく既存 headline だった** — 旧名 bc_converse は degraded
    限定なのに名前がそう言っておらず、**無条件の一般 BC converse `bc_capacity_subset_uv` と紛れる**。
    consumer が 0 → 1 に変わる leg が最後の安い時機で、`bc_degraded_converse` へ改名した。
    ⟹ **安い時機は「新規宣言のとき」ではなく「consumer が付く前」**。
    ⊕ **最悪の形は「同一 namespace で同じ語が正反対を指す」** — MAC の軸別達成/converse は
    `axis1` / `axis2` を達成側では「沈黙するユーザー」、converse 側では「生きている座標」の意味で
    使っており、**同じ namespace 内で番号が反転していた**。解消は語彙ごと捨てて下付き = **生きている
    座標**に統一 (`mac_rate₁/₂_achievable` / `mac_timesharing_converse_rate₁/₂`) ⟹ 一般則:
    **番号付きの対称な宣言では「番号が何を数えているか」を宣言名の規約として先に固定する**。
27. **在庫 / plan が `docs/rules/` より厳しい自前ルールを書くと、後続 leg を不要に縛る**: more capable
    在庫 §Q8 の「600 行を超えたら 2 分割」は `docs/rules/module-structure.md` の閾値 (1500 行) にも
    拘束条件 (**関心の混在**であって行数ではない) にも反していた。⟹ 一般則: **規約の SoT は
    `docs/rules/` 側**。数値の閾値を書くときは「規約のどの条文の言い換えか」を明示し、言い換えで
    ないなら**その leg 限りの目安**と明記する。`MoreCapable.lean` の将来の切れ目だけは決定済 =
    `MoreCapable/{Comparison,Equality}.lean` (`{Region,Assembly}` は `Superposition/` と紛らわしい)。
28. **検証バーの「warning 0」は既存 warning のある家系では成立しない — 正しい基準は「既存からの
    増分 0」**: F-20 が定めた linter 設定では BC 家系の既存ファイルに warning が実在する。⟹ 確認手順は
    **HEAD 版を `git show` で取り出して同一設定で lint し、warning 集合が完全一致することを見る**
    (件数の暗記ではない — 件数は触るたび動く機械再導出可能値)。⊕ 2 つの実務則、**どちらも Phase 2 の
    style ゲートで再現した** (`d0c02420` / `93a3a6fb`): (a) **`set_option linter.unusedSectionVars false`
    で抑止せず section を入れ子に割って消すと、必要な型クラス束の実測値が副産物として残る** (抑止と
    分割は warning が消える点では同じでも情報量が違う)、(b) **証明冒頭の `classical` で `DecidableEq`
    は埋まる** (Phase 2 では `MartonUnion.lean` の `[DecidableEq]` 3 本が両 headline の署名から消えた)。
29. **汎用補題を `private` で書くと、別 family が同じ補題を局所再導出する — `private` 解除は
    「その leg の都合」に見えて実は死に在庫の解消**: degraded 接続が必要とした
    `isMarkovChain_of_append` / `kernel_compProd_prodMkRight_eq_prod` は
    `Achievability/Assembly.lean` の `private` で、`private` は**namespace ではなく file スコープ**
    (CLAUDE.md §Project Layout) だから新規ファイルからは import しても呼べない。移設 (public 化 +
    `Shannon/CondEntropyMemoryless.lean` へ上流移動) の副産物として、**WynerZiv が同じ 2 本を
    別名で逐語コピーしていた**ことが判明し、削除して上流版に張替えた (`86b90af1`)。⟹ 一般則:
    **BC 固有語を含まない補題を `private` にするときは file スコープの含意を 1 度確認する** — この種の
    重複は `dep_consumers.sh` にも名前検索にも映らず (名前が違う)、**結論形で探して初めて出る**。
    ⊕ **P7 で同じ機構が「在庫の *無い*」側に出た (在庫は編集しないので本エントリが記録)**: 在庫 §9-2 の
    「entropy の測度についての連続性は in-repo に該当なし」は `rg "Continuous.*entropy|Tendsto.*entropy"`
    の**名前語順の都合**で外れており、実際には MAC に `macMix_entropy_continuous` +
    `macInfo₁/₂/Both_perturb_continuous` が在った。結論形 (`Continuous (fun ε ↦ entropy …)`) で引けば
    出る。同じ leg で `martonJointDistribution_real_singleton` も**同名・同結論で既存**だった
    (`Marton/MarkovCore/Prelim.lean`)。さらに P7 が要した部品一式 — MAC の汎用混合 API と、**同じ
    定理の MAC 版** `mac_pentagon_subset_capacityRegion_allprob` — が追加の橋 0 行でそのまま効いた。
    ⟹ 一般則: **在庫の「無い」は名前検索の否定であることが多く、結論形で引き直すまで採らない**
    (CLAUDE.md「In-repo asset search」の plan 版)。
    ⊕ **家系をまたぐと「同名・同命題」の重複も生き残る**: `entropy_le_log_card` は SlepianWolf と
    MaxEntropy に 1 本ずつあり、`#check` で並べて初めて**型クラス前提まで完全同一**と分かった
    (宣言行だけ読むと `variable` 束の差が見えず判断できない) ⟹ **重複疑いの 2 本は宣言行ではなく
    `#check` で diff する** (CLAUDE.md「In-repo asset search」の 2 項目め)。
