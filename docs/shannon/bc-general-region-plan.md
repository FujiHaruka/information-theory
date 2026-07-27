# Shannon: 一般 BC 容量領域フレーム サブ計画

> **Parent**: [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md) §L-BC5 後続

未解決問題「一般 2 受信者 BC の容量領域の特徴づけ」に対して形式化が提供できるのは **足場**
(内界 / 外界 / 両者による挟み込み) までで、未解決本体 (内外一致) は数学が存在しないので Phase 外。
本計画はその足場を組む。到達目標は `martonRegion W ⊆ bcCapacityRegion W ⊆ bcOuterRegion W` を
Lean の 1 本の定理列として持つこと。

## 進捗

- [x] Phase 1 操作的容量領域 (主語) ✅ `fd39ad95` `deb930a7`
- [ ] Phase 2 補助変数 union 📋 **Phase 5 の等号の前提** (park 不可、判断ログ 11-(k))
- [x] Phase 3 協調外界 (安い外界) ✅ `e9222d0a` `b9ba272a`
- [x] Phase 4a UV 単一文字化 (floating 形) ✅ `5bf64adf` `f7023332` `bff554c2` `33ec3522` `54705cb3`
- [x] Phase 4b UV 外界の集合化 + 操作的包含 ✅ `6ddb1a48` `bfdd55e1` `c768cc00` (**全平面版**)
- [ ] Phase 5 一致クラスの拡張 🚧 ★現在の本線
  - [x] 定義段 (符号規約の対称化 + 3 クラス + 包含鎖) ✅ `2c938fe0` `91fd8dcf` `e6ff1963` `42ac21e7`
  - [x] 内外を同じ添字に載せる橋 S1–S4 ✅ `6b0c1ea1` `76b83bc1` `0186b708`
  - [ ] 等号 (容量領域の一致) 📋 — 残りは S5 (和レート不等式) → S6 (領域包含)。Phase 2 が前提

## 在庫

| 資産 | 場所 | 用途 |
|---|---|---|
| `BCAchievable` / `bcCapacityRegion` | `BroadcastChannel/Operational.lean:53` / `:68` | 主語。Phase 3/4b の包含の左辺 |
| `bc_capacityRegion_isClosed` / `bc_achievable_mono` / `bc_mem_closure_of_strictly_below` | `Operational.lean:102` / `:71` / `:86` | 閉性・down-set 性・厳密不等号からの closure 回収 |
| `martonRegion` / `bc_strict_interior_achievable` / `marton_region_subset_capacity` | `Operational.lean` (168 行 / 8 decl) | 内界の集合版と包含 (`@[entry_point]`)。**符号制約なしの全平面版** (`2c938fe0`、判断ログ 12) |
| **比較クラス 3 本 + 包含鎖** | `BroadcastChannel/Classes.lean` (253 行 / 9 decl、import 2 本) | `IsBCLessNoisy:63` / `IsBCMoreCapable:75` / `IsBCSemiDeterministic:83` と `@[entry_point]` 4 本 `bc_lessNoisy_infoJoint_ge:95` / `IsBCDegraded.isBCLessNoisy:133` / `IsBCLessNoisy.isBCMoreCapable:218` / `IsBCSemiDeterministic.exists_prob_real_singleton_eq_zero:236`。語彙橋 2 本 `bcJointDistribution_id_eq:166` / `mutualInfoOfChannel_map_eq_mutualInfo_bcJointDistribution:184` が `bcJointDistribution` 語彙と `mutualInfoOfChannel` 語彙を繋ぐ |
| `bcOuterRegionCoop` / `bc_capacity_subset_coop` | `OuterBound.lean:380` / `:408` | 協調外界と包含 (`@[entry_point]`)。挟み込みの右辺 |
| `BroadcastCode.restrict₁/₂` / `coop` + 誤り確率補題 | `OuterBound.lean:50`–`:262` | BC 符号 → 単一ユーザー符号への 3 通りの還元 |
| `channelCoding_operational_rate_le_capacity` | `ChannelCoding/StrongConverseAsymptotic.lean:805` | 操作的レート ≤ 容量 (`@[entry_point]`)。Phase 3 の心臓 |
| `uvAux` | `OuterBoundUV.lean:71` | UV 補助変数。**型が letter `i` に依存する** (S5 の型統一の理由) |
| `bc_uv_singleletterize_r1/_r2/_sum₁/_sum₂` | `OuterBoundUV.lean:113` / `:174` / `:684` / `:637` | 単一文字化 4 本 (corner 2 + sum-rate 2)、degradedness 前提なし |
| `InBCOuterRegionUV` / `bc_uv_converse` | `OuterBoundUV.lean:735` / `:815` | UV 外界の 4 不等式束と メッセージレベル headline (`@[entry_point]`) |
| **符号→ambient の共有層 (S1)** | `ChannelCoding/CodeToAmbient.lean` (539 行 / 15 decl、MAC/BC 共有) | `isMarkovChain_of_compProd_pi:210` (conditioner 一般形) / `isMemorylessChannel_of_compProd_pi:322` / `le_log_of_ceil_exp_le:518`。分割 A で BC 由来の汎用 3 本が合流 (`compProd_comap_map_prodMap:346` / `compProd_pi_map_pair_eq_of_update_invariant:396` / `le_toReal_of_inv_mul_le:528`) |
| **BC の符号→ambient 橋 (S2–S6)** | `BroadcastChannel/OuterBoundUV/Bridge.lean` (936 行 / 58 decl) | `bcConverseAmbient:141` → 構造前提 4 本 `:301`–`:428` → `bcConverseFanoSlack₁/₂:532`/`:541` → `bc_uv_converse_from_code:562` / `bc_uv_rate_extract:602` → `uvAuxPad:663` + 不変性 `:713`–`:738` |
| **UV per-letter 情報スロット (S6)** | 同ファイル `:764`–`:934` (`section PerLetterInfo`) | `uvInfo₁:777` / `uvInfo₂:782` / `uvInfoSum₂:787` / `uvInfoSum₁:792` (5 つ組法 `ν` の 1 引数汎関数) + `bcUVTuple:809` / `bcUVJointDistribution:833` + 同定 4 本 `:849` / `:867` / `:884` / `:909` |
| **UV 外界の集合版 (S7)** | `BroadcastChannel/OuterBoundUV/Region.lean` (474 行 / 33 decl) の `section ChannelLaw` / `section Region` / `section NotVacuous` + `Assembly.lean` (851 行 / 35 decl) の `section CodeLaw` | チャネル整合条件 `IsUVChannelLaw:102` + 特徴づけ `isUVChannelLaw_iff:123` + 閉包性 5 本 (`.smul` / `.add` / `.finsetSum` / `.map_auxiliaries` / `.map_input_output`)。領域 `uvRegion:233` / `bcOuterRegionUV:245` / `_isClosed:251` / `_isLowerSet:265` / `_nonempty:317`。非退化の証拠 `not_isUVChannelLaw_uvOutputCopiesInputLaw:363` / `not_isUVChannelLaw_uvAuxCopiesOutputLaw:438`。符号側の支払い `bcUVJointDistribution_isUVChannelLaw` だけは符号に依存するので `Assembly.lean:72` に残る |
| **時間共有 + 平均化 (S8-a)** | `Assembly.lean` の `section AuxRelabel` / `section TimeSharing` (汎用の混合法補題は `Shannon/CondMutualInfoMixture.lean` へ分離) | 混合法 `bcUVTimeShare:258` (+ `_isUVChannelLaw:284` / `_eq_sum:272`) と 4 スロットの平均化 `bcUVTimeShare_uvInfo₁_ge:315` / `_uvInfo₂_ge` / `_uvInfoSum₂_ge` / `_uvInfoSum₁_ge`。補助アルファベットの `ℕ` 付け替え `uvRelabel:134` + スロット不変 4 本 |
| **極限 + 退化被覆 + headline (S8-b)** | `Assembly.lean` の `section TimeSharing` 後半 / `section Operational` (パディングは `BroadcastChannel/Basic.lean` へ分離) | 縮小点の**乗法形** `bc_uv_code_point_mem:609` → `bc_uv_rate_point_mem:635` → `bc_uv_shifted_point_mem:696` (極限) → `bc_uv_quadrant_mem_of_achievable:784` → headline `bc_capacity_subset_uv:839` (`@[entry_point]`、本ファイル唯一)。退化被覆は `bc_achievable_clamp_iff:670` + 下方集合性、`2 ≤ M` の穴は `BroadcastCode.padFirst`/`padSecond` (`Basic.lean:127`/`:134`) + 誤り確率補題 2 本 |
| 汎用資産 (S7/S8 自作、BC 非依存) | `CodeToAmbient.lean`: `compProd_comap_map_prodMap` / `compProd_pi_map_pair_eq_of_update_invariant` / `le_toReal_of_inv_mul_le`。`Shannon/CondMutualInfoMixture.lean` (193 行 / 7 decl): 再符号化不変 3 本 `mutualInfo_eq_of_leftInverse:40` / `mutualInfo_congr_ae:57` / `condMutualInfo_eq_of_leftInverse_cond:66` + 混合法 4 本 `condDistrib_compProd_fst_ae_eq:91` (private) / `condMutualInfo_compProd_fst_eq_lintegral:102` / `mutualInfo_compProd_eq_add_lintegral:142` / `condMutualInfo_compProd_snd_eq_lintegral:164` | Mathlib 不在で自作。`compProd_pi_map_pair_eq_of_update_invariant` は同ファイル `compProd_pi_map_pair_eq:366` の strict generalization (監査が機械確認、統合は §後続作業 D)。`condMutualInfo_compProd_*_eq_lintegral` は**絶対連続性の仮説を持たない等式**。BC 側からの移設は分割 A で完了 |
| `csiszar_sum_identity_cond` | `OuterBoundUV/Gateway.lean:246` | 条件付き Csiszár 和恒等式 (異アルファベット + 背景 conditioner)。Phase 4a の核 |
| `csiszar_sum_identity` | `BroadcastChannel/ConverseGateway.lean:142` | 無条件版 (同一アルファベット) |
| `bc_converse` / `bc_input_singleletterize` | `BroadcastChannel/Converse.lean:571` / `:316` | degraded 限定の converse。Phase 5 の接続先。**これも floating 形** |
| `bc_achievability` | `BroadcastChannel/Achievability/Assembly.lean:1093` | degraded 限定の達成側。Phase 5 の接続先 |
| `marton_achievability` | `Marton/Achievability.lean:767` | 一般 BC 内界 (EGK Thm 8.3、private message のみ) |
| `InMartonRegion` | `Marton/Basic.lean:40` | 3 不等式バンドル (点ごと述語) |
| **内外の橋 (S1–S4)** | `OuterBoundUV/MartonBridge.lean` (261 行 / 16 decl、import 1 本) + `Region.lean:203` | 内界の法を外界の `ℕ` 添字に載せる層。`martonJointDistribution_isUVChannelLaw:67` (`@[entry_point]`) → `martonSwapLaw:114` (+ instance / `_isUVChannelLaw:127`) → `martonUVLaw:157` + `martonUVLaw_isUVChannelLaw:174` (`@[entry_point]`)。4 スロット保存 `uvInfo₁_martonUVLaw:183` 系 4 本 + `.toReal` 同定 3 本 `martonInfo₁_eq_uvInfo₁_toReal:225` / `martonInfo₂_eq_uvInfo₂_toReal:237` / `martonInfoV₁V₂_eq_mutualInfo_toReal:249`。入替不変性の一般形だけは `IsUVChannelLaw.swap_auxiliaries` (`Region.lean:203`) |
| `MACAchievable` / `macPentagon` / `macCapacityRegion` | `MultipleAccess/TimeSharing.lean:49` / `:58` / `:66` | 操作的述語 → closure で集合化のパターン |
| **MAC の符号→ambient 橋** | `MultipleAccess/TimeSharingConverse/Bridge.lean` (847 行 / 37 decl) | **S6 の雛形 (消化済)**。per-letter 同定は `macConverse_map_triple_eq:718` → 同定 3 本 `:771` / `:797` / `:823` |
| **MAC の集合化 + 極限** | `MultipleAccess/TimeSharingConverse/Assembly.lean` (953 行 / 12 decl) | S8-a までの雛形。`bc_capacity_subset_uv` の対応物は `mac_timesharing_converse:817` / `mac_timesharing_capacity_region:908` — ただし後者は**第一象限交差版**で、MAC はそもそも退化レートを被覆していない (判断ログ 11-a)。`:397`–`:817` の約 420 行は「軸上の点」用であって退化被覆の一般解ではなく、**S8-b では不採用** |
| `mac_avgPentagon_mem_convexHull` | `TimeSharingConverse/Bridge.lean:99` | n 文字平均を単一文字分布の凸包へ落とす先例。**4b では不採用** (案 A = 時間共有変数の補助変数への吸収を採ったため) |
| `mac_capacity_region_reconciliation` | `MultipleAccess/Reconciliation.lean:292` | 内外を同じ言語に揃える先例 |

**存在しないもの** (Phase 5 の等号が要求し、まだ書かれていないもの): (a) 内界側の補助変数 union
(= Phase 2)、(b) more capable の 3 制約を受ける structure (`InBCCapacityRegion` は 2 field)、
(c) 和レート制約の情報量不等式 (S5) — 内界の `boundSum` 1 本と外界の `uvInfoSum₂` / `uvInfoSum₁`
2 本は**別の汎関数**なので `.toReal` の同定では埋まらない (判断ログ 14)、
(d) `IsBCDegraded W` から `bcConverseAmbient` 上の per-letter Markov 鎖 `h_deg_block` を出す補題
(`bcConverse_deg*` は 0 hit)、(e) `(mutualInfo μ Xs Xs).toReal = entropy μ Xs` と決定的写像の条件付き
エントロピー消失 (semi-deterministic の `H(Y₁)` 用)。**Mathlib 側の穴はゼロ** (在庫 §6、壁 0 件)。
クラス定義そのものは `Classes.lean` で実在化済。

## ゴール / Approach

**「まず外界」は半分正しい。その前に主語が要る。**

Approach は **「主語 → 安い外界で挟み込みの骨格 → 本命の外界 → 一致クラスの拡張」** の 4 段。
外界の重い仕事の前に Phase 1 で `bcCapacityRegion W : Set (ℝ × ℝ)` を定義し、Phase 3 の緩い外界で
**一度挟み込みを完成させてしまう**。以後の外界の改良はすべて「同じ挟み込みの右辺を狭める」差分
作業になり、1 本ごとに独立して価値が出る。逆順 (先に UV outer bound を作る) だと、最も重い Phase
が最初に来るうえ、完成しても内界と並べられない。この順序は Phase 1/3 の実績で正当化された。

**Phase 4 を 4a / 4b に割る**、というのが現時点での構造上の主判断。外界には 2 つの独立した層が
あり、難所が別物だから:

- **情報量レベル (4a)** — 補助変数の identification と単一文字化。難所は Csiszár 和恒等式の
  適用形。ambient 測度 `μ` を「与えられたもの」として受け取る floating 形で完結する。
- **操作的レベル (4b)** — `bcCapacityRegion ⊆ bcOuterRegionUV`。難所は符号から ambient 測度を
  構成する橋と、n 文字の平均を単一文字補助変数の分布へ落とす還元。情報量そのものの議論は増えない
  が、**どの形の点を領域に入れるかは極限の可否を決める**ので設計判断が残る (判断ログ 11-b)。

Phase 3 がこの分割を要求しなかったのは、Wolfowitz strong converse の対偶を使うことで **ambient
の構成を丸ごと迂回できた**から。Fano ベースの UV 外界では同じ手が使えず、橋が不可避になる。
なお degraded 版 `bc_converse` も floating 形で止まっているが、**4b の橋がそのまま効くわけではない**
— `bc_converse` は degradedness を ambient 上の per-letter Markov 鎖 `h_deg_block` で受けており、
`bcConverse_*` にはこれを出す補題が無い (判断ログ 11-(n))。

## Phase 詳細

### Phase 1 — 主語を作る (操作的容量領域) ✅

`fd39ad95` `deb930a7`。`BCAchievable` / `bcCapacityRegion := closure {…}` / `martonRegion` を定義し、
`marton_region_subset_capacity` で内界を集合の言葉に載せた。副産物として `marton_achievability`
から使われていない正値仮説 2 本を除去 (定理が強くなる方向、consumer 0 件)。
proof-log: no (MAC の写経で設計判断が無かったため)。

### Phase 2 — 補助変数についての union (**Phase 5 の等号の前提**) 📋

`martonRegion` は `(pV, K)` を引数に取る。真の Marton 内界は補助変数の型と分布についての和集合。

- [ ] 型量化の回避: `V₁ V₂ : Type*` の量化は universe 問題を生むので、濃度を `Fin k` に固定して
      `k` について union する形を採る
- [ ] Carathéodory 型の濃度上界 (補助変数のアルファベットを入力アルファベットで抑える) は
      Mathlib にも in-repo にも無い。**自作コストが読めないので、濃度固定版で止めるのが honest**
- [ ] time-sharing / convex hull が要るなら `MultipleAccess/TimeSharingConverse/` の資産を参照

**挟み込み (Phase 3 / 4b) の前提ではない** — そこは Phase 1 の点ごとの形で言える。だが
**Phase 5 の等号の前提ではある**: 外界 `bcOuterRegionUV` は補助変数についての union の closure、
内界 `martonRegion` は `(pV, K)` 1 個ぶんの四辺形なので、等号を述べるには内界側にも union が要る
(判断ログ 11-(k))。等号を「∃ pV K」形で述べて union を回避する道もあるが、その形は教科書の内界より
弱い主張になるので、採るなら plan に明記すること。
proof-log: no。

### Phase 3 — 協調外界 (安い外界) ✅

`e9222d0a` `b9ba272a`。BC 符号を 3 通り (受信機 1 のみ / 受信機 2 のみ / 出力対を 1 出力と見る協調
受信) に還元し、`bcOuterRegionCoop` + `bc_capacity_subset_coop` を得た。単一ユーザー側の入口として
`StrongConverseAsymptotic.lean:805` に `channelCoding_operational_rate_le_capacity` を新設。
**これで `martonRegion ⊆ bcCapacityRegion ⊆ bcOuterRegionCoop` の挟み込みが完成**し、未解決問題の
全景が (緩い外界ながら) Lean に載った。proof-log: no。

### Phase 4a — UV 単一文字化 (floating 形) ✅

`5bf64adf` `f7023332` `bff554c2` `33ec3522` `54705cb3`。`OuterBoundUV.lean` (938 行) +
`OuterBoundUV/Gateway.lean` (315 行)。補助変数を `uvAux` 1 本に統一 (受信機 1 出力の prefix と
受信機 2 出力の suffix を共有し、運ぶメッセージだけが違う) したことで、当初「3 本を同時に扱う」と
見積もっていた identification が 2 本の instantiation に縮んだ。核は新規自作の
`csiszar_sum_identity_cond` (既存 `csiszar_sum_identity` の異アルファベット + 背景 conditioner への
二重の一般化)。headline `bc_uv_converse` は **degradedness 前提なし**、構造前提は memoryless 2 本 +
encoder Markov 2 本のみ。proof-log: no (単一文字化の機構は docstring に収まった)。

### Phase 4b — UV 外界の集合化 + 操作的包含 ✅ CLOSED

`6ddb1a48` (実装) / `bfdd55e1` `c768cc00` (両ゲート)。到達目標を**全平面版**で達成した:

```lean
@[entry_point]
theorem bc_capacity_subset_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    bcCapacityRegion W ⊆ bcOuterRegionUV W
```

明示仮説は `W` と `[IsMarkovKernel W]` のみ (第一象限制約も符号仮説もなし)。これで
**`martonRegion ⊆ bcCapacityRegion ⊆ bcOuterRegionUV`** が成立し、Phase 3 の
`bcOuterRegionCoop` 版と 2 本並立になった。

| step | 成果 | commit |
|---|---|---|
| M0 在庫 | [`bc-uv-operational-inventory.md`](bc-uv-operational-inventory.md) — MAC 橋の全 decl を `reuse` / `mirror` / `restructure` / `absent` に分類。**Mathlib 側に自作が要る穴はゼロ** | — |
| S1 共有化 | `ChannelCoding/CodeToAmbient.lean` 新設 (MAC/BC 共有)。MAC `Bridge.lean` の汎用補題 11 本を移設して public 化 | `278977c2` `1c6c69aa` |
| S2 BC ambient 構成 | `OuterBoundUV/Bridge.lean` 新設。出力空間を `Fin n → β₁ × β₂` に固定した結果 `bcConverseKernel c W m = c.blockOutputLaw W m` が `rfl` | `a6fd1ec5` |
| S3 構造前提の導出 | 難所 1。構造前提 4 本 (`h_memo₁/₂` `hmarkov₁/₂`) を ambient の構成から導出。**`OuterBoundUV.lean` は無改変** | `6275f2bb` `2e5b248f` |
| S4 符号レベル converse | `bcConverse_errorProb₁/₂_eq` + `bc_uv_converse_from_code` (`@[entry_point]`) + `bc_uv_rate_extract` | `51d5bcf9` |
| S5 補助変数の型統一 | 難所 2。`uvAuxPad` + 相互情報量 / 条件付き相互情報量の不変性 (L-BCO5 不発動) | `5fd4d3ce` `4fd80cd3` |
| S6 per-letter 同定 | `uvInfo₁/₂/Sum₁/Sum₂` + `bcUVTuple` / `bcUVJointDistribution` + 同定 4 本。**自作補助補題ゼロ** | `c67f756c` `45807dcc` |
| S7 集合化 | `OuterBoundUV/Assembly.lean` 新設。判断ログ 9 の 2 条件を `IsUVChannelLaw` = 1 本の合成積恒等式で同時に課し、反例 class ごと閉じた | `e9682e21` `d0418dbd` `ae72035d` |
| S8-a 情報量の平均化 | 時間共有済み混合法 `bcUVTimeShare` + 4 スロットの `(n)⁻¹ ∑ᵢ slotₖ(νᵢ) ≤ slotₖ(mixture)` | `31b8d2a3` `a069be70` `c65b7094` |
| S8-b 極限 + 退化被覆 | 難所 3。縮小点を**乗法形**に差し替えて極限に乗せ (判断ログ 11-b)、退化被覆は `bc_achievable_clamp_iff` + 領域の下方集合性で約 15 行、`2 ≤ M` の穴は `padFirst` / `padSecond` で 55 行。**L-BCO6 不発動** | `6ddb1a48` `bfdd55e1` `c768cc00` |

**領域定義の確定形 (Phase 5 が参照する SoT)**:

```
bcOuterRegionUV W = closure (⋃ (ν : ProbabilityMeasure (ℕ × ℕ × α × β₁ × β₂))
                               (_ : IsUVChannelLaw W ↑ν), uvRegion ↑ν)
uvRegion ν = {p | InBCOuterRegionUV p.1 p.2 (uvInfo₁ ν).toReal (uvInfo₂ ν).toReal
                    (uvInfoSum₂ ν).toReal (uvInfoSum₁ ν).toReal}
```

closure は不可避 (半平面の交差の union は閉じない) だが、それが `bcOuterRegionUV_isClosed` を
無料にし `bcCapacityRegion = closure {achievable}` との接続 (`IsClosed.closure_subset_iff`) に効く。
**第一象限制約なし** (判断ログ 1) + **下方集合** (`bcOuterRegionUV_isLowerSet`) の 2 点が S8-b の
コストを決めた。`uvInfoSum₁/₂` の**下付き数字は受信機番号ではなく「先頭に来る corner 項の選択」**
(両方とも `R₁ + R₂` の上界)。宣言順は `InBCOuterRegionUV` のフィールド順に合わせた意図的なもの。

proof-log: **yes** (`docs/proof-logs/proof-log-bc-uv-operational.md`、別 dispatch)。書くべき要点は
4 つ — (a) 在庫予測の外れ 2 件 = MAC 雛形の前提誤り / 「極限を取るだけ」の誤り (判断ログ 11)、
(b) 外界に符号制約を入れなかった判断が退化被覆を約 15 行に収めた機構 (判断ログ 1)、
(c) S8-a の `h_ac` が `by_cases` で消えた経緯 (判断ログ 11 の 5 件目)、
(d) 橋 (S1–S4) を MAC から読み替えたときに何が効かなかったか (degraded 側 `bc_converse` への
再利用も、仮説の表現が違うぶんそのままでは効かない = 判断ログ 11-(n))。

### Phase 5 — 一致するクラスを広げる 🚧 ★本線

degraded は既に閉じている。その一般化を、Phase 1 の内界と Phase 4b の外界の組で回収する。
Phase 5 は **定義段 (完遂) → 等号 (未着手)** の 2 段で、両段の間に Phase 2 が挟まる。

#### 定義段 ✅ (`2c938fe0` `91fd8dcf` `e6ff1963` `42ac21e7`)

M0 在庫は [`bc-phase5-class-inventory.md`](bc-phase5-class-inventory.md) (Mathlib の壁 0 件)。

| step | 成果 | commit |
|---|---|---|
| 符号規約の対称化 | `martonRegion` から `0 ≤ p.1 ∧ 0 ≤ p.2` を除去。`marton_region_subset_capacity` は署名無修正で通り、証明は 2 行が 1 行に畳まった。direct consumer 1 decl / 1 file (`dep_consumers.sh` 実測、在庫予測と一致)。**これをやるまで等号はどのクラスでも述べられなかった** (判断ログ 12) | `2c938fe0` |
| クラス 3 本 + 包含鎖 | `Classes.lean` 新設。`IsBCLessNoisy` (補助変数を量化する結合法版) / `IsBCMoreCapable` (`mutualInfoOfChannel` によるチャネル版) / `IsBCSemiDeterministic` (`Kernel.fst W a = dirac (f a)`) + `degraded ⊆ less noisy ⊆ more capable` が機械可読に成立。**proof done** (0 sorry / 0 `@residual`) | `91fd8dcf` |
| 両ゲート | honesty **all OK** (tier 5 なし、`@audit:ok` 9 箇所) / style PASS | `e6ff1963` `42ac21e7` |

**等号 (容量領域の一致) はまだ述べていない**。README 定理表への登録は**保留** — 包含鎖は headline
としては弱く、等号が閉じた段で `docs/readme-theorems.txt` に入れるのが自然 (現時点で未編集)。

#### 等号 📋 — 攻略順は **less noisy → more capable → semi-deterministic**

- [ ] **前提 = Phase 2 (内界側の union)**。外界は union、内界は四辺形 1 個なので、そのままでは
      等号が型として並ばない (判断ログ 11-(k))
- [x] **内外を同じ添字に載せる橋 (橋 S1–S4)** ✅ `6b0c1ea1` (在庫) `76b83bc1` (実装) `0186b708` (style)。
      M0 在庫は [`bc-inner-outer-bridge-inventory.md`](bc-inner-outer-bridge-inventory.md) (Mathlib の壁 0 件)。
      内訳は S1 Marton 結合法が `W` のチャネル法 (**入替不要** — `IsUVChannelLaw` は補助 2 スロットを
      ブロックとしてしか見ないので、入替が要るのは情報量スロットを読むときだけ) / S2 入替不変性の
      一般形 / S3 `ℕ` 添字化 + 4 スロット保存 / S4 情報量 3 本の `.toReal` 同定。配置と宣言は §在庫。
      両ゲートは honesty が launch 条件外 (新規 sorry も既存署名の変更もない) + style PASS。
      予測と実測の差は判断ログ 14
- [ ] **橋 S5 = 和レート不等式** (本命の数学、予想 150–250 行)。S3 の 4 スロット保存が通った結果
      **S5 が負うのは `condMutualInfo` 半分だけに縮んだ**: `uvInfoSum₂ ν = uvInfo₂ ν + I(X;Y₁ | 第 1 スロット)`
      で、入替法では第 1 スロット = `V₂` ⟹ `uvInfo₂` 半分はちょうど `martonInfo₂` (S4 で同定済)。
      `uvInfoSum₁` 側も対称に `martonInfo₁` + `I(X;Y₂ | V₁)`。残る需要は 2 本 —
      **A**: `martonInfo₁ - martonInfoV₁V₂ ≤ (condMutualInfo (martonSwapLaw …) X Y₁ V₂).toReal` /
      **B**: `martonInfo₂ - martonInfoV₁V₂ ≤ (condMutualInfo (martonSwapLaw …) X Y₂ V₁).toReal`。
      経路は `mutualInfo_chain_rule` (`CondMutualInfo.lean:214`) 2 本で挟み `mutualInfo_le_of_markov`
      (`CondMutualInfo.lean:356`) の DPI + `IsMarkovChain` の構成という 5 step (在庫 §6-2 に逐語)。
      **`ℕ` 化には一切触れなくてよい** — 4 スロット保存は S3 で全部通っているので S5 は
      `martonSwapLaw` 上だけで完結し、S6 が最後に 4 本を `rw` するだけで union に入る。
      `condMutualInfo_map_comp` (`CodeToAmbient.lean:465`) の `StandardBorelSpace` 要求は
      `MartonBridge.lean` の変数ブロックから自動導出される (`uvInfoSum₂_martonUVLaw` が実際に
      それで通った) ので**追加仮説は不要**。詰んだ場合の退避は `sorry` +
      `@residual(plan:bc-marton-uv-sum-bound)` で、**S6 の署名は保つ**
- [ ] **橋 S6 = 領域包含** `martonRegion pV K W ⊆ bcOuterRegionUV W` (`@[entry_point]` 候補、予想 40 行)。
      S5 の 2 本 + S4 の同定 3 本を `rw` して `subset_closure` に載せる。**逆包含は L-BCO8**
- [ ] **less noisy** (Körner–Marton 1975/1977) — 容量領域は degraded と**同じ 2 制約**に落ちる。
      UV の 4 制約が corner 2 本に落ちるので、既存の結論形をそのまま再利用できる。
      内界側の全支持仮説とも両立する (degraded の全支持例が存在) ⟹ **最も再利用率が高い**
- [ ] **more capable** (El Gamal 1979) — **「単純化」ではなく「形が違う」**。制約は 4 → 3 に減るが、
      うち 1 本 `R₁ + R₂ ≤ I(X;Y₁)` は**補助変数を含まない**新しい形で、`InBCCapacityRegion`
      (2 field) では受けきれず **3 field の新 structure が要る**。UV の `uvInfoSum₁` の
      `V = X` 特殊化で到達可能ではある
- [ ] **semi-deterministic** (Marton 1979) — 定義は入ったが**内界の定理が適用できない**。
      `marton_achievability` / `marton_region_subset_capacity` の全支持仮説
      `hW : ∀ a b, 0 < (W a).real {b}` を定義上必ず破る (in-tree の証拠 =
      `IsBCSemiDeterministic.exists_prob_real_singleton_eq_zero`、判断ログ 13) ⟹ 等号は
      **L-BCO7** で defer し、外界側だけで止める
- [ ] **degraded との接続は「新規配線の作成」**。`bc_converse` / `bc_achievability` はどちらも
      direct consumer 0 件 (`dep_consumers.sh` 実測) で、合流先の配線が存在しない。さらに
      `bc_converse` の degradedness は `IsBCDegraded` (チャネルレベル) ではなく `h_deg_block`
      (ambient 上の per-letter Markov 鎖) なので、**4b の橋 (S1–S4) はそのままでは効かない** —
      `bcConverse_memoryless₁/₂` / `isMarkovChain₁/₂` に対応する degradedness 版が 0 hit で、
      `isMarkovChain_of_compProd_pi` パターンの新規 ~120 行が要る (判断ログ 11-(n))
- [x] **`uvRegion` の `.toReal` は決着済** (S8-a / S8-b の honesty 監査からの引き継ぎ): `⊤ ↦ 0` は
      外界を**縮める**ので逆包含では保護側に働き、有限アルファベットの Phase 5 では `⊤` 自体が
      起きない。危険は無限アルファベット (`StandardBorelSpace` 側) への拡張の 1 軸だけ
      (判断ログ 11-(m)、§設計上の未決事項)

proof-log: 定義段と橋 S1–S4 は no。等号 (橋 S5–S6) が閉じたら yes。

## 後続作業 (Phase 5 の前提ではない)

style / honesty ゲートが提起して当該 leg では見送った項目 + 分割 A の実施後に立った flag。
完了したものは 1 行 + commit に圧縮して残す (項目番号は他文書が参照するので付け替えない)。

### A. `Assembly.lean` の二段分割 ✅ 完了

`210b7558` (一段目) → `e163853d` (style) → `69cc5b10` (死んだ import 掃除) → `5c121f95` (二段目) →
`3af79fea` (style)。Assembly 1588 → **851 行**、全ファイルが 1500 行ガイド内。汎用ブロックは
`Shannon/CondMutualInfoMixture.lean` (新規) / `ChannelCoding/CodeToAmbient.lean` /
`BroadcastChannel/Basic.lean` へ、領域定義 3 section は `OuterBoundUV/Region.lean` (新規) へ。
**純粋な移設で新しい数学は 0 行 / 新規 sorry 0 / `@audit:ok` は逐語保存**、`bc_capacity_subset_uv`
(唯一の `@[entry_point]`) は Assembly 残留。現在の配置は §在庫 が SoT。予測と実測の差は判断ログ 11。

### B. 命名 / 死んだ宣言 (**波及がほぼ 0 の今なら事実上無料**)

1. **`bc_uv_rate_extract` (`Bridge.lean:602`、`@audit:ok`) が dead** — Assembly が
   `bc_uv_converse_slots` に乗り換えた結果、direct consumer **0**
   (`scripts/dep_consumers.sh` 実測)。削除 or 保持の判断が要る
2. **`*_point_mem` 5 本の命名** (`bc_uv_{mixture,shrunk,code,rate,shifted}_point_mem`、5 本とも
   分割後も `Assembly.lean` 在住 `:429` / `:565` / `:609` / `:635` / `:696`) — 形容詞が
   段階を系統的に区別しておらず名前だけでは判別不能。`docs/rules/naming.md` §2 は判別子を仮定側に
   置けと定める (`bc_uv_mem_of_letterSum_le` 等)。**波及ほぼ 0**: `bc_uv_shrunk_point_mem` のみ
   docs 3 本が参照、残り 4 本は Assembly 外の参照ゼロ
3. `uvAux_pad_mutualInfo_prod_eq` (`Bridge.lean:723`) の `prod` が何の直積か名前から読めない
   (実際は左引数で補助変数と `Xs` を対にする)。`uvAux_pad_pair_mutualInfo_eq` 等へのリネーム提案。
   consumer は in-file 1 件 (`uvAux_pad_condMutualInfo_eq:738`、`dep_consumers.sh` 実測)
4. **命名の軽微な逸脱** `condMutualInfo_eq_of_leftInverse_cond` — `naming.md` §2 は `_of_` 以降を
   仮定列に充てるので、区別子 `_cond` は `_of_` の**前**に置くのが Mathlib 順。優先度低。
   在住は分割 A で `Assembly.lean` → **`Shannon/CondMutualInfoMixture.lean:66`**。移設は逐語で
   行いリネームしていないので「移すついでに直す」機会は過ぎた ⟹ 単独のリネーム leg になる

### C. 数学的な締めどころ / その他

1. **`bcConverseFanoSlack₁_le` が 2 bit 捨てている** — `Real.log (M₁ - 1) ≤ Real.log M₁` への緩和で、
   `M₁ = 2` では左辺が 0。converse の結論には効かない (余裕は十分) が、将来レートの 2 bit 残差を
   詰めたくなったときの最初の締めどころ
2. `bcOuterRegionUV ⊆ bcOuterRegionCoop` を示せれば「UV は協調外界より狭い」が機械可読になる
   (**任意**。示せなくても挟み込みは 2 本並立で成立する)
3. `CodeToAmbient.lean` の MAC 由来 6 本 (`compProd_pi_map_pair_eq` / `mutualInfo_map_comp` /
   `condDistrib_map_comp` / `condMutualInfo_map_comp` / `condMutualInfo_map_comp'` /
   `le_log_of_ceil_exp_le`) が無タグ。分割 A で合流した BC 由来 3 本のうち 2 本は `@audit:ok` を
   逐語で持って来たが `le_toReal_of_inv_mul_le` は無タグなので、対象は 7 本 (実測)。file 全体の
   タグ被覆を揃えるなら別 leg。同ファイルに
   `show` → `change` の linter 警告が 1 件 (`lake build` でのみ出る)
4. **section 再配置による逐語コピーの完全畳み込み (残 ~30 行)**。
   `∑ i, uvInfo₁ (bcUVJointDistribution c W i)` 形への完全な畳み込みは現配置では不可能 —
   `bcUVJointDistribution` は `uvAuxPad` に依存し、`uvAuxPad` は `bc_uv_converse_from_code` より
   **後ろ**にある。取りに行くなら `section Pad` + `section PerLetterInfo` を `section CodeLevel` の
   **上**へ移す再配置が要る
5. **規約どうしが同じケースで逆方向に引く件 (S8-a で実測データが揃った)**:
   `docs/rules/docstrings.md` item 1 (`## Main statements` 掲載定理には docstring 必須) と
   `scripts/lean_doc_lint.ts` の `internal-doc` ratchet (内部補題の散文 docstring 増加を NG とする)
   が構造的に衝突する。リンターは module doc の Main statements リストを見ないので、
   `@[entry_point]` もタグも無い theorem に散文 docstring を足すと 1 本あたり `internal-doc` +1。
   S8-a で `bc_uv_shrunk_point_mem` が通ったのは `@audit:ok` タグがあったから
   (`lean_doc_lint.ts:469`–`:478` が `@residual|@audit:` を含む docstring を skip する) で、
   一般には通らない。**Main statements 掲載でタグ無しが 6 本裸** — 分割 A で 3 ファイルに散った
   (実測): `Region.lean` の `isUVChannelLaw_iff:123` / `not_isUVChannelLaw_uvOutputCopiesInputLaw:363` /
   `not_isUVChannelLaw_uvAuxCopiesOutputLaw:438`、`CondMutualInfoMixture.lean` の
   `condMutualInfo_compProd_fst_eq_lintegral:102` / `condMutualInfo_compProd_snd_eq_lintegral:164`、
   `Assembly.lean` の `bcUVTimeShare_uvInfo₁_ge:315` 系。**分割は衝突を再生産する** — 新ファイルの
   module doc は Main statements を書き直すので、そこに載る宣言が新たに裸のまま増える。
   解は「真の headline に `@[entry_point]` を付ける (リンターが除外)」か
   「module doc に散文を持たせる現行慣行を追認する」の二択で、ファイル単体を超える方針判断
   = **本 plan の範囲外** (`docs/rules/` 側の課題として起票)。
   **前者を実践した最初の事例が `Classes.lean`** — `## Main statements` に載る 4 本すべてに
   `@[entry_point]` が付いており (リンターは entry_point を無条件で除外)、新規ファイル 9 宣言で
   `internal-doc` ratchet への寄与は **0**、衝突は 1 本も発生しなかった (style ゲート実測)。
   新規ファイルを切るときの既定手として使える

### D. 汎用補題の置換統合 (分割 A とは別 leg、未着手)

分割 A は**移設だけ**を行い、重複する一般形 / 特殊形の統合は手つかず。数学は増えず consumer の
書き換えだけがコストなので、着手判断は純粋に波及の大きさで決まる。

| 統合 | 被置換側の consumer (`dep_consumers.sh` 実測) |
|---|---|
| `compProd_pi_map_pair_eq_of_update_invariant` (`CodeToAmbient.lean:396`) は**同ファイル** `compProd_pi_map_pair_eq:366` の strict generalization | direct **1 decl / 1 file** (`TimeSharingConverse/Bridge.lean:712` = `macConverse_map_triple_eq`)、**transitive 12 decl / 2 file** (MAC `Bridge.lean` 4 本 + MAC `Assembly.lean` 8 本 = `mac_timesharing_capacity_region` まで到達) |
| `mutualInfo_eq_of_leftInverse` (`CondMutualInfoMixture.lean:40`) は `MIChainRule.lean:35` の `mutualInfo_map_left_measurableEquiv` (より強い `MeasurableEquiv` 仮説) を subsume | direct **17 decl / 11 file** — BC 系 4 file (`Converse` / `ConverseGateway` / `OuterBoundUV` 3 本 / `OuterBoundUV/Gateway` 2 本) + MAC 系 3 file + WZ 系 1 file + chain-rule 系 3 file |

**2 本目は import 面の判断が先**: 両ファイルは兄弟 (`MIChainRule` → `MutualInfo`/`CondMutualInfo`/
`Entropy`、`CondMutualInfoMixture` → `CondKLIntegral`/`CondMutualInfo`) で循環はしないが、
consumer に `MIChainRule.lean:73` 自身が含まれるため、置換すると **chain-rule ハブに KL-integral
依存が入る**。§後続作業 A が `CondMutualInfo.lean` 本体への合流を却下したのと同じ理由なので、
**1 本目 (同ファイル内で完結) だけ先に切る**のが安い。

### E. 分割 A が新たに立てた flag (どちらも行数圧力ゼロ、優先度低)

1. **`CondMutualInfoMixture.lean` はファイル名と中身が一致していない** — 7 宣言のうち mixture は
   4 本で、残り 3 本 (`mutualInfo_eq_of_leftInverse` / `mutualInfo_congr_ae` /
   `condMutualInfo_eq_of_leftInverse_cond`) は**再符号化不変性**で mixture に一切触れない。
   コンパイラで見える決定的な tell: **`Bridge.lean` は本ファイルを `mutualInfo_eq_of_leftInverse` の
   ためだけに import しており (参照は `:719` / `:731` の 2 箇所のみ、実測)、mixture 補題を 1 本も
   使っていない**。分割案 = `Shannon/MutualInfoReencoding.lean` (再符号化 3 本) + 現ファイル
   (mixture 4 本、前者を import)。consumer が既に綺麗に分かれている (Bridge → 再符号化のみ /
   Assembly → 両方) ので循環は生じない。**193 行で行数圧力はゼロ**なので急がないが、consumer が
   2 ファイルだけの今が最も安い。着手時は判断ログ 11 の (i) を先に適用すること
   (新ファイルの import は consumer 表ではなく**移動先が引かざるを得ない依存の閉包**で決まる)
2. **`open scoped BigOperators` が tree 全体で死んでいる** — 今の Mathlib では `∑`/`∏` 記法が
   global。style ゲートが `Region.lean` から外して EXIT=0 を確認したが、同じ open を持つファイルが
   **189 本** (実測) あり数ファイルだけ外すと不揃いになるので戻した。tree 一括 sweep
   (一括置換 + `lake build` 1 回) として別 leg にするのが筋で、BC 固有ではないので**本 plan の
   範囲外** (起票先は `docs/rules/` 側)

### F. Phase 5 (定義段 + 橋 S1–S4) が新たに立てた flag

1. **`bcJointDistribution_id_eq` (`Classes.lean:166`) のリネーム (style ゲートが「今が最安」と推奨)** —
   裸の `_eq` で右辺が名前に出ず、内部橋なので docstring も無い ⟹ 名前が statement を語れていない。
   **consumer は同ファイル内 1 箇所のみ (外部参照ゼロ、`rg` 実測)**。代案
   `bcJointDistribution_id_eq_map_compProd`。「1 行 docstring を足す」路は §C-5 の `internal-doc`
   ratchet が増えて `--check` が落ちるので取れない ⟹ **リネームが唯一の解**
2. `bc_lessNoisy_infoJoint_ge` (`Classes.lean:95`) / `bc_degraded_infoJoint_ge`
   (`Achievability/Assembly.lean:965`) の `_of_` 化 — `docs/rules/naming.md` §2 の厳密形は
   `bc_infoJoint_ge_of_lessNoisy`。**2 本同時リネームか両方現状維持かの二択** (対の名前が割れるのが
   最悪。style の推奨は現状維持)
3. 語彙橋 2 本 (`bcJointDistribution_id_eq` / `mutualInfoOfChannel_map_eq_mutualInfo_bcJointDistribution`)
   を `private` にするか。将来 §5-5 の内外橋がこれらを引くなら public のまま。優先度低
4. `IsBCSemiDeterministic.exists_prob_real_singleton_eq_zero` に `_of_one_lt_card` を付けるか (任意)
5. **README 定理表への登録は保留** (オーケストレーター判断) — 定義段の包含鎖は headline としては
   弱く、等号が閉じた段で登録するのが自然。`docs/readme-theorems.txt` は未編集

以下 3 件は橋 S1–S4 の style ゲートが提起。リネーム 2 件はどちらも**参照が `MartonBridge.lean` 内で
閉じており外部 consumer 0** (`rg` 実測) = 今が最安。

6. **`auxNatIndex` → `natIndex` (推奨度 中)** — 定義は `Fintype.equivFin X x` で任意の `Fintype X` に
   総称であり、「補助変数の」は使用側のラベルにすぎない。加えて Mathlib 慣行の `aux` = 繋ぎ宣言と
   読めるので `docs/rules/naming.md` の proof-staging 語彙の隣に落ちる
7. **`martonSwapLaw` → `martonAuxSwapLaw` (推奨度 低)** — 何を swap したのかが名前に出ていない
8. **§C-5 の規約衝突が本 leg でも再現し、機械側に従った** — `docs/rules/docstrings.md` item 1 は
   headline を「`@[entry_point]` **または** module doc の `## Main statements` 掲載」と定義して
   docstring を必須とするが、`scripts/lean_doc_lint.ts` の `internal-doc` ratchet (`:476`) は
   `@[entry_point]` かタグ持ちだけを headline と見なす。本 leg の 4 宣言 (`martonInfo*_eq_*` 3 本 +
   `swap_auxiliaries`) がその隙間に落ち、最初の版が PostToolUse hook に BLOCK された ⟹ **リンターを
   実装 SoT として裸のままにした**。散文規則の側を立てるなら安い手は docstring 追加ではなく
   `martonInfo*_eq_*` 3 本への `@[entry_point]` 付与だが、これは headline 認定の判断なので未着手。
   BC 固有ではなくツリー全体の規約ギャップ (§C-5 と同一の軸、起票先は `docs/rules/` 側)

## 未解決本体との距離 (正直な見積り)

「Marton 内界 = 一般 BC の容量領域か」は **open**。数学が存在しないので形式化できない。本計画が
終わっても未解決問題は未解決のままで、得られるのは以下。

- 内界・外界・容量領域が同一言語で並び、**ギャップが機械可読な形で固定される**
- 特定の BC で内外が分離するかを検証する基盤 (反例候補の検算)
- 一致が既知の特殊クラスについては、等号が実際に閉じる (Phase 5)

期待値は「厳密な足場 + 教材価値」に置くのが妥当。形式化が情報理論の未解決問題の解決に直接
寄与した前例は無い、という前提で計画している。

## 設計上の未決事項

1. **補助変数 union の射程** (Phase 2) — 濃度固定で止めるか Carathéodory を自作するか。
   等号の前提になったので、決めるのを先送りできなくなった
2. **more capable の容量領域を受ける structure** (Phase 5) — 3 制約 (うち 1 本は補助変数を
   含まない `R₁ + R₂ ≤ I(X;Y₁)`) なので `InBCCapacityRegion` を拡張するか新 structure を建てるか
3. **`martonInfo*` を `ℝ≥0∞` の `mutualInfo` / `condMutualInfo` 版へ pivot するか** (L-BCO8 の代替の
   攻め筋) — 逆包含の `Fintype ℕ` 閉塞を型ごと消せる。1 と排他ではなく (Carathéodory 型の濃度上界と
   定義 pivot はどちらでも逆包含が開く二択)、判断材料は `marton_achievability` 側への波及の実測

`uvRegion` の `.toReal` を `ℝ≥0∞` 版に移すかは**決着** — Phase 5 (有限アルファベット) では
無関係で、判断が要るのは `StandardBorelSpace` 側への拡張に進むときだけ (Phase 5 の項)。
Phase 4b の 2 件 (単一文字還元の形 / 結合 memoryless の持ち方) も決着済 (案 A 採用 / 構成側で
持つ、S3 で機械確認)。履歴は git。

## 撤退ライン (frozen slug)

| slug | 発動条件 | 退避先 |
|---|---|---|
| **L-BCO1** | Phase 4 の補助変数 identification が閉じない | **不発動** — Phase 4a で `uvAux` 1 本の 2 通り instantiation により閉じたため、Körner–Marton / Sato への後退は不要になった |
| **L-BCO2** | Phase 2 の型量化 union が universe 問題で詰む | 濃度固定版で止め、union は取らない。**「Phase 3–5 は影響を受けない」は誤りだったので撤回** — 影響を受けないのは Phase 3 / 4 (挟み込み) だけで、**Phase 5 の等号は union を前提とする** (判断ログ 11-(k))。この撤退を取ると等号は「∃ pV K」形の弱い主張に落ちる。**実質的に前倒しで解けている公算**: `IsBCLessNoisy` は補助を `U : Type u` (入力アルファベットと同 universe) に量化する形で着地し、honesty 監査が **`Type u` 版 ⟹ 任意 universe 版**を probe のコンパイルで確認した (ULift 経由の relabel 不変性 = `Fintype.equivFin` + `Equiv.ulift` + `compProd_comap_map_prodMap` 2 回 + `mutualInfo_map_comp`)。**この probe は in-tree に落ちていない = 未 in-tree の機械確認**なので、Phase 2 で同じ手を採るなら改めて書き下すこと |
| **L-BCO3** | Phase 5 の等号が Phase 4 の外界の形と噛み合わない | クラス定義だけ入れて等号は defer。**発動条件の文言は実態とずれている** (在庫 §7): 噛み合わなさの本体は外界の形ではなく**内界の形** (符号制約 = `2c938fe0` で解消 / union なし = Phase 2 / 全支持仮説 = L-BCO7) だった。slug は凍結なので文言はそのまま残し、判定は内界側の 3 点で行う |
| **L-BCO4** | Phase 4b の符号→ambient 橋または単一文字還元が閉じない | **不発動のまま Phase 4b が完遂** — 橋は S1–S4、集合化は S7、平均化は S8-a、極限と包含は S8-b でいずれも closure した |
| **L-BCO5** | S5 の補助変数の型統一が `mutualInfo_chain_rule` 経由でも閉じない | **不発動** — 在庫の攻略路 (両向き DPI + `mutualInfo_chain_rule` + `ENNReal.add_right_inj`) がそのまま効いた。退避先だった「`n` を露出した族 `bcOuterRegionUVAt W n` + `⋂ n` 版」は採らない (slug は他文書参照のため凍結) |
| **L-BCO6** | S8-b の退化レート被覆が MAC 同様 450 行級に膨らむ | **不発動** — 退避先だった第一象限交差版は採らず、`bc_capacity_subset_uv` は**全平面版**で closure した (退化被覆の実測は約 15 行 + `2 ≤ M` の穴埋め 55 行、判断ログ 1) |
| **L-BCO7** | semi-deterministic の等号を狙う段で、`marton_achievability` の全支持仮説 `hW` が外せない (判断ログ 13) | **semi-deterministic はクラス定義 + 外界側だけで止め、等号は述べない**。外界 (`bc_capacity_subset_uv` の特殊化) は `hW` を要求しないので単独で成立する。退避の出口は `sorry` + `@residual(plan:bc-semideterministic-fullsupport)` (= `hW` を外す後継 plan のファイル名 stem)。**`IsSemiDeterministicAchievable` のような述語に核を束ねる形は取らない**。**橋は本ラインの外**: 橋 S1–S4 は `hpV` / `hK` / `hW` を 1 本も要求しない (判断ログ 15) ので semi-deterministic チャネルでも成立する ⟹ L-BCO7 が止めているのは内界の**達成側** `marton_achievability` だけで、発動判定はその 1 点で行う |
| **L-BCO8** | 等号の逆包含 (`bcOuterRegionUV W ⊆ ⋃ martonRegion`) を書く段で、`bcOuterRegionUV` の `ℕ` 補助を `martonInfo*` の `[Fintype]` 要求に合わせられない (Carathéodory 型の濃度上界が要る)。**機械確認済**の逐語エラーは `failed to synthesize instance of type class Fintype ℕ` (在庫 §4-B)。**universe 問題ではないので L-BCO2 の発動条件では拾えない** — これが別 slug を立てる理由 | **順包含側 (橋 S6 = `martonRegion ⊆ bcOuterRegionUV`、`Fintype` 側から `ℕ` へ**降りる**向き) だけで止める**。逆包含は `sorry` + `@residual(plan:bc-marton-uv-cardinality-bound)` で**署名を保つ**。**退避前に 1 度試す代替**: `martonInfo*` を `ℝ≥0∞` の `mutualInfo` / `condMutualInfo` 版に置き換える定義 pivot (`mutualInfo` は `[Fintype]` 不要を逐語確認済)。ただし `marton_achievability` (`Marton/Achievability.lean:767`) が `martonInfo*` を仮説に持つので `scripts/dep_consumers.sh` の実測が先。**`IsMartonCoverable` のような述語に「逆包含が成り立つ」を束ねる形は取らない** |

**active な撤退ラインは L-BCO2 / L-BCO3 / L-BCO7 / L-BCO8 の 4 本** (Phase 2 用 1 本 + Phase 5 用 3 本)。

**禁止事項**: どの撤退でも「外界が成立する」「補助変数が取れる」「符号から ambient が取れる」等を
`*Hypothesis` 述語に束ねて仮説として渡す形は取らない (CLAUDE.md 検証の誠実性 tier 5)。退避は
`sorry` + `@residual` で、署名は証明したい形のまま保つ。Phase 5 で等号を述べる段では、クラス条件
(less noisy 等) を「等号が成り立つ」に近い形の述語で受け取っていないかを毎回確認する。

## 推奨実行順

定義段と橋 S1–S4 まで到達した。**残りは橋の内側の 2 step (S5 → S6) と、その先の等号 (Phase 2 を通る)**:

```
Phase 5 定義段 ✅ → 内外の橋 S1–S4 ✅ (Marton 法を UV チャネル法として ℕ 添字に載せる)
  ↓
橋 S5 (和レート不等式 = 本命の数学。負うのは condMutualInfo 半分だけ)   ← ★次の一手
  ↓
橋 S6 (martonRegion ⊆ bcOuterRegionUV、@[entry_point] 候補)  ← 順包含は union 不要
  ↓
Phase 2 (内界側の補助変数 union)   ← 等号そのものの前提。ここが park 可でなくなった
  ↓
less noisy の等号 → more capable の等号 (3 field の新 structure) → semi-deterministic は L-BCO7
                    (逆包含 bcOuterRegionUV ⊆ ⋃ martonRegion が詰んだら L-BCO8)
```

**橋 S5 / S6 は Phase 2 を待たない** — 順包含は `Fintype` 側から `ℕ` へ降りる向きなので内界の union が
要らない。**Phase 2 が前提になるのは等号を述べる段**で、挟み込み (Phase 3 / 4b) の前提でないのは変わらない。
§後続作業 B–F はいずれも前提ではない (F-1 / F-6 / F-7 のリネームだけは consumer が in-file の今が最安)。

## 判断ログ

1. **外界に第一象限制約を入れない — この判断が S8-b のコストを決めた (成功要因の記録)**:
   `bcCapacityRegion` は**非正レート対を真に含む** (単一メッセージ符号で達成可能、Phase 1 の
   独立監査が特定)。外界に `0 ≤ R` を入れると包含が偽になるので、Phase 3 も S7 も符号制約を
   入れない形を採った。
   **後段の払い戻し (S8-b 実測)**: 符号制約がない ⟹ 領域が**下方集合**
   (`bcOuterRegionUV_isLowerSet`) ⟹ 退化レート被覆が `bc_achievable_clamp_iff` (非正レートを 0 に
   丸めても達成可能性は不変) + 下方集合性で**約 15 行**。MAC が軸ごとの片側 converse に約 420 行を
   要したのは、外界側に `0 ≤ R` が入っていて軸上の点を直接入れられなかったからで、**より強い形を
   選ぶ判断が後段のコストを下げた実例**になった。
   `2 ≤ M` の穴は `BroadcastCode.padFirst` / `padSecond` (1 メッセージ符号に第 2 メッセージを足す。
   2 つを同じ符号語で送り `decoder₁` は定数) で埋めた (計 55 行)。効く算術は「**2 メッセージ受信機の
   Fano たるみは `binEntropy Pe ≤ log 2` で誤り確率によらず定数 1 bit**」で、監査が「パディング後の
   誤り確率はちょうど 1/2」を probe のコンパイルで確認済。
9. **union の添字を縛る 2 条件は `IsUVChannelLaw` 1 本 = 単一の合成積恒等式で解決した (S7)**:
   `uvInfo*` は 5 つ組法 `ν` の 1 引数汎関数でチャネル `W` を引数に取らないため、union を無制約に
   取ると出力を入力にコピーする `ν` が 4 スロットを任意に大きくでき、**外界が平面全体に退化して
   `bc_capacity_subset_uv` が vacuous に真になる** (アルファベット拡大で無限に構成できる反例 class)。
   S7 は要る 2 条件 (出力の条件法が `W` に一致 / 補助 → 入力 → 出力の Markov 性) を別々の述語に
   せず 1 本の等式で同時に課し、`isUVChannelLaw_iff` が「union の添字は**補助と入力の任意の同時法を
   チャネルに通したもの ちょうど**」を与えて反例 class ごと閉じた (監査が機械確認)。非退化の証拠は
   `not_isUVChannelLaw_uvOutputCopiesInputLaw` / `not_isUVChannelLaw_uvAuxCopiesOutputLaw` として
   code 側に named theorem で残っている。監査の判定は「`IsUVChannelLaw` は load-bearing hyp ではなく
   **包含の右辺を縮める構造条件**」— 符号側で構成的に示す義務は
   `bcUVJointDistribution_isUVChannelLaw` として支払い済。**Phase 5 が外界の形を触るときは、この
   特徴づけが壊れないかが最初のチェック点**。
11. **在庫予測の外れ (通算 16 件) — 在庫ファイル自体は編集しないので本エントリが記録の SoT**。
    S8-b までの 5 件は (a) 一般化の方向が 1 段広かった (S3、conditioner を任意の
    update 不変写像に開く形になり整形層が丸ごと消えた) / (b) `macConverseInput_eq` = `absent` は
    誤りで対一様性は受信機別の誤り確率同定**両方**に要った (S4) / (c) union の無制約化で外界が
    平面全体に退化する反例 class が在庫に載っていなかった (S6→S7、判断ログ 9) / (d) 0-hit 見落とし /
    (e) 在庫が名指しした危険 (`h_ac`) が `by_cases` の否定側で **∞ = ∞** に落ちて丸ごと消え、
    `condMutualInfo_compProd_fst_eq_lintegral` は絶対連続性の仮説を持たない等式になった (S8-a、
    over-estimation 側)。S8-b の 2 件:
    - **(f) MAC 雛形の前提が誤っていた**: 本 plan と実装ブリーフは MAC
      `TimeSharingConverse/Assembly.lean` の約 420 行を「退化レート被覆の雛形」としていたが、
      **MAC はそもそも退化レートを被覆していない** — `mac_timesharing_capacity_region` 自身が
      第一象限交差版で、MAC は最初から L-BCO6 相当を選んでいた。あの 420 行は「MAC の縮小点補題が
      `0 ≤ R₁` と `0 ≤ R₂` を**同時に**要求する」ことの帰結 = 軸上の点を入れるための補題であって、
      退化被覆の一般解ではない。**BC には移植不要だった**。
      ⟹ 雛形を参照するときは「その雛形の**到達目標が自分と同じ強さか**」を先に確認する。
    - **(g)「極限を取るだけ」が誤り**: 本 plan は S8-b を「点列の極限を取るだけで情報量の議論は
      増えない」としていたが実測は否。`bc_uv_shrunk_point_mem` の**加法形** (両座標から `(F₁+F₂)/n`
      を引く) は極限に乗らない — `F₂` は `Pe₂ * Real.log (M₂ - 1)` を含み、`BCAchievable` は `M₂` を
      **下からしか**縛らないので `Real.log M₂` が非有界 ⟹ `F₂/n` が 0 に行かない。受信機 1 の座標に
      受信機 2 の未制御なたるみが混入するのが原因。修正は**乗法形**
      `(Real.log Mₖ * (1 - Peₖ) - 2 * Real.log 2) / n` への差し替え (新設 `bc_uv_code_point_mem`)。
      **BC に足りなかったのは MAC の軸機構ではなく縮小点の「形」だった**。
      ⟹ 一般教訓: **前 step の到達点が次 step の入口として使えるとは限らない**。到達点が無条件宣言で
      あっても、次段が要求する性質 (ここでは各項が 0 に行くこと) を持つとは限らない。step 境界では
      「前 step の結論の**形**が次 step の入口として妥当か」を独立に確認する。

    分割 A (移設リファクタ) の 3 件。**3 件とも「宣言の配置を変えると何が起きるか」の読み違い**で、
    数学ではなくファイル境界に関する予測が外れた:
    - **(h)** consumer 表は**移す decl 全部**を行にする (§後続作業 A の表は同じ leg で移す
      `compProd_comap_map_prodMap` を落としていた)。1 本でも欠けると表が「網羅」の役を果たさない。
    - **(i) import の必要性は consumer 表では決まらない** — 決めるのは**移動先ファイルが他に何を
      import せざるを得ないかの閉包**。`Region.lean` は `uvInfo₁/₂` のために `Bridge.lean` を引かざるを
      得ず、その `Bridge` 経由で `CodeToAmbient` に推移的に届いていた (明示 import は規律上望ましい
      だけでコンパイル上は必須ではなかった)。
    - **(j)** 移設は移動元の import を殺す (実測 4 本、うち Mathlib 2 本、`69cc5b10`)。
      ⟹ 移設 leg には最初から「移動元の import 生死を実測する」step を入れる。

    Phase 5 の M0 在庫 ([`bc-phase5-class-inventory.md`](bc-phase5-class-inventory.md) §10) が
    挙げた 8 件のうち、2 件は独立の判断として下記 12 / 13 に立てた。残る 6 件:
    - **(k) Phase 2 は Phase 5 の等号の前提だった**: plan は「Phase 2 は Phase 3–5 の前提ではない」
      としていたが、正しいのは**挟み込みについてのみ**。外界は補助変数についての union、内界は
      `(pV, K)` 1 個ぶんの四辺形なので、等号を述べる段では内界側にも union が要る。
      ⟹ **「独立」「park 可」の判定は到達目標ごとに違う**。同じ Phase が、ある到達目標には
      無関係で別の到達目標には前提になる。park 判定は目標を名指して書く。
    - **(l) more capable は「単純化」ではなく「形が違う」+ 文献帰属が 1 件誤り**: plan は
      「more capable / less noisy — 外界が UV より単純 (El Gamal 1979)」としていたが、less noisy は
      **Körner–Marton 1975/1977** (El Gamal 1979 は more capable)。かつ more capable の容量領域は
      3 制約で、うち `R₁ + R₂ ≤ I(X;Y₁)` は**補助変数を含まない新しい形** ⟹ 制約の本数は減るのに
      受け皿の structure は新設が要る。「制約が減る = 簡単」ではない。
    - **(m) `.toReal` の危険の向きが逆だった**: plan は逆包含 (領域 ⊆ operational) の段で
      `.toReal` が「逆向きに効く」としていたが、`⊤ ↦ 0` は外界を**縮める**ので逆包含は易しくなる
      = 保護側。危険は無限アルファベット拡張の 1 軸だけ。
      ⟹ 「非対称性がある」と気づいた時点で止めず、**どちらの向きに倒れるかまで言い切る**こと。
    - **(n) 4b の橋は degraded 側にそのままでは効かない**: plan は「`bc_converse` も floating 形
      なので 4b の橋 (S1–S4) が効く」としていたが、`bc_converse` の degradedness は
      `IsBCDegraded` (チャネルレベル) ではなく `h_deg_block` (ambient 上の per-letter Markov 鎖)。
      `bcConverse_*` 4 本に対応する degradedness 版は 0 hit で、新規 ~120 行が要る。
      ⟹ **「同じ floating 形だから橋が効く」は形の一致であって仮説の一致ではない**。
      再利用可否は結論形ではなく**要求される仮説の表現**で決まる。
    - **(o) 部品は在庫に載っていた**: 「クラス定義は project に 0 hit」は述語としては正しいが、
      more capable の定義に要る `Kernel.fst W` / `Kernel.snd W` は `bcOuterRegionCoop` で既に
      使用済だった (本 plan の §在庫 に記載が無かった)。定義コストは想定より小さかった。
    - **(p) 「既存に接続」の実体は新規配線**: `bc_converse` / `bc_achievability` はどちらも
      direct consumer 0 件 (`dep_consumers.sh` 実測)。合流先の配線が存在しないので、見積りは
      「接続」ではなく「新規実装」で立てる。
12. **片側で採った規約変更は、対になるもう片側にも適用したか確認する (P1、`2c938fe0` で解消)**:
    判断ログ 1 は「外界に第一象限制約を入れない」判断を成功要因として記録しているが、**同じ判断を
    内界に適用する step が無かった** — `martonRegion` だけが第一象限のまま残り、結果
    `bcOuterRegionUV ⊆ martonRegion` は**どの `W` でも偽**だった (在庫が `(-1,-1)` で機械確認)。
    Phase 5 の等号はどのクラスでも述べられない状態で、気づかずに等号へ着手すれば全チャネルで偽の
    目標を追うことになっていた。修正は定義の 1 行削除で、consumer 1 decl は符号成分を既に捨てて
    いたので署名も証明も壊れていない (`marton_region_subset_capacity` は**内界を広げる方向**なので
    真のまま — 非正レートは単一メッセージ符号で達成可能)。
    ⟹ 一般教訓: **規約 (符号制約・座標順・`ℝ` / `ℝ≥0∞` の別) を片側で変えたら、対になる側との
    差分を必ず 1 度取る**。片側だけの規約変更は、両者を並べる定理を書こうとする段まで発覚しない。
13. **semi-deterministic は内界の定理と構造的に非両立 (P3、L-BCO7 を新設)**:
    plan は semi-deterministic を「Marton 内界 = 容量領域が既知」として Phase 5 の第一候補格に
    挙げていたが、`marton_achievability` / `marton_region_subset_capacity` の全支持仮説
    `hW : ∀ a b, 0 < (W a).real {b}` を **semi-deterministic は定義上必ず破る** (`Y₁ = f(X)` なので
    到達しない出力対の質量が 0)。内界の包含そのものが使えないので、等号は閉じない。in-tree の証拠は
    `IsBCSemiDeterministic.exists_prob_real_singleton_eq_zero`。攻略順を
    **less noisy → more capable → semi-deterministic** に変更し、最後の 1 本は L-BCO7 で defer する。
    ⟹ 一般教訓: **「文献で容量領域が既知」と「in-project の内界定理が適用できる」は別**。
    クラスを候補に挙げる前に、そのクラスが**既存定理の regularity 前提と両立するか**を先に見る
    (CLAUDE.md textbook-object strength diff の適用先が、定理の強度ではなく**前提の両立性**だった例)。
14. **「内外の橋は `mutualInfo_toReal_eq_entropy_form` 1 本のみ」は 3/4 だけ正しかった (橋 S1–S4)**:
    3 スロット (`martonInfo₁` / `martonInfo₂` / `martonInfoV₁V₂`) には確かに 1 本 6 行で足りる (S4 で
    機械確認) が、**和レート制約には対応物が存在しない** — 内界は `boundSum` の `I₁+I₂-I₁₂` 1 本、
    外界は `uvInfoSum₂` / `uvInfoSum₁` の 2 本で**別の汎関数**。`.toReal` の橋では埋まらず情報量
    不等式の自作 (橋 S5) が要る ⟹ 前 leg の「橋は安い」という見立ては 3/4 だけ正しかった。
    **行数の予測 → 実測**: S1 50→45 / S2 30→22 / S3 40→95 / S4 25→35。S3 / S4 の超過は数学ではなく
    **署名の反復** (`(pV …) [IsProbabilityMeasure pV] (K …) [IsMarkovKernel K] (W …) [IsMarkovKernel W]`
    が 8 宣言に付く) で、証明本体はどれも 2–5 行。
    ⟹ 一般教訓: **「同定 1 本で済む」の見積りは、内外の制約が同数・同形かを先に数えてから立てる**。
    本数が違う (内界 3 本 vs 外界 4 本) 時点で、余った 1 本が別の数学であることは確定していた。
15. **橋は内界側の全支持仮説を 1 本も要求しない ⟹ L-BCO7 は緩む方向 (橋 S1–S4)**:
    S1–S4 の明示仮説は `pV` / `K` / `W` と `[IsProbabilityMeasure pV] [IsMarkovKernel K]
    [IsMarkovKernel W]` だけで、`hpV` / `hK` / `hW` は 1 本も現れない (署名走査で実測)。
    ⟹ **semi-deterministic チャネルでも橋は成立する**。L-BCO7 が止めているのは内界の**達成側**
    `marton_achievability` であって橋ではない。
    ⟹ 一般教訓: **撤退ラインは「どの宣言が止まるか」まで降ろして書く**。「クラス X では内界が
    使えない」の粒度だと、実際には無関係な後続 step まで巻き込んで park することになる。
