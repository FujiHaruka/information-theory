# Shannon: 一般 BC 容量領域フレーム サブ計画

> **Parent**: [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md) §L-BC5 後続

未解決問題「一般 2 受信者 BC の容量領域の特徴づけ」に対して形式化が提供できるのは **足場**
(内界 / 外界 / 両者による挟み込み) までで、未解決本体 (内外一致) は数学が存在しないので Phase 外。
本計画はその足場を組む。到達目標は `martonRegion W ⊆ bcCapacityRegion W ⊆ bcOuterRegion W` を
Lean の 1 本の定理列として持つこと。

## 進捗

- [x] Phase 1 操作的容量領域 (主語) ✅ `fd39ad95` `deb930a7`
- [ ] Phase 2 補助変数 union 🚧 — **最小完遂 P1–P3 ✅** `ce8e9d0b` `fcdafaf5` `b1837901` / 拡張 P4–P7 📋
- [x] Phase 3 協調外界 (安い外界) ✅ `e9222d0a` `b9ba272a`
- [x] Phase 4a UV 単一文字化 (floating 形) ✅ `5bf64adf` `f7023332` `bff554c2` `33ec3522` `54705cb3`
- [x] Phase 4b UV 外界の集合化 + 操作的包含 ✅ `6ddb1a48` `bfdd55e1` `c768cc00` (**全平面版**)
- [ ] Phase 5 一致クラスの拡張 🚧 ★現在の本線
  - [x] 定義段 (符号規約の対称化 + 3 クラス + 包含鎖) ✅ `2c938fe0` `91fd8dcf` `e6ff1963` `42ac21e7`
  - [x] 内外を同じ添字に載せる橋 S1–S6 ✅ `6b0c1ea1` `76b83bc1` `0186b708` `28eae4ea`
  - [ ] 等号 (容量領域の一致) 📋 ★次の一手 — 攻略順は less noisy → more capable

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
| **内界の union (Phase 2 の P1–P3)** | `BroadcastChannel/MartonUnion.lean` (110 行 / 5 decl、import 2 本) | `bcAuxAlphabet:52` (`= ULift.{u} (Fin (k+1))`) / `martonRegionUnion:58` / `martonRegionUnionFS:68` (全支持添字のみ) + `@[entry_point]` 2 本 `martonRegionUnion_subset_uv:81` (明示仮説ゼロ) / `martonRegionUnionFS_subset_capacity:101` (`hW` のみ) + `_subset_union:88`。`Marton/` 配下ではなくトップ直下 (§Phase 2) |
| `marton_achievability` | `Marton/Achievability.lean:767` | 一般 BC 内界 (EGK Thm 8.3、private message のみ) |
| `InMartonRegion` | `Marton/Basic.lean:40` | 3 不等式バンドル (点ごと述語) |
| **内外の橋 (S1–S6、全段 proof done)** | `OuterBoundUV/MartonBridge.lean` (553 行 / 32 decl、import 1 本) + `Region.lean:203` | 内界の法を外界の `ℕ` 添字に載せ、順包含まで運ぶ層。S1–S3 = `martonJointDistribution_isUVChannelLaw:70` (`@[entry_point]`) → `martonSwapLaw:117` (+ instance / `_isUVChannelLaw:130`) → `martonUVLaw:160` + `martonUVLaw_isUVChannelLaw:177` (`@[entry_point]`) + 4 スロット保存 `uvInfo₁_martonUVLaw:186` 系 4 本。S4 = `.toReal` 同定 3 本 `:228` / `:240` / `:252`。S5 = 和レート 4 本 `martonInfo₁_sub_martonInfoV₁V₂_le:447` / `…₂…:469` / `martonInfoSum_le_uvInfoSum₂_toReal:493` / `…₁_toReal:509` (核は Markov 鎖 2 本 `:303` / `:329` + 条件付き DPI)。S6 = `marton_region_subset_uv:530` (`@[entry_point]`)。入替不変性の一般形だけは `IsUVChannelLaw.swap_auxiliaries` (`Region.lean:203`) |
| `MACAchievable` / `macPentagon` / `macCapacityRegion` | `MultipleAccess/TimeSharing.lean:49` / `:58` / `:66` | 操作的述語 → closure で集合化のパターン |
| **MAC の符号→ambient 橋** | `MultipleAccess/TimeSharingConverse/Bridge.lean` (847 行 / 37 decl) | **S6 の雛形 (消化済)**。per-letter 同定は `macConverse_map_triple_eq:718` → 同定 3 本 `:771` / `:797` / `:823` |
| **MAC の集合化 + 極限** | `MultipleAccess/TimeSharingConverse/Assembly.lean` (953 行 / 12 decl) | S8-a までの雛形。`bc_capacity_subset_uv` の対応物は `mac_timesharing_converse:817` / `mac_timesharing_capacity_region:908` — ただし後者は**第一象限交差版**で、MAC はそもそも退化レートを被覆していない (判断ログ 11-a)。`:397`–`:817` の約 420 行は「軸上の点」用であって退化被覆の一般解ではなく、**S8-b では不採用** |
| `mac_avgPentagon_mem_convexHull` | `TimeSharingConverse/Bridge.lean:99` | n 文字平均を単一文字分布の凸包へ落とす先例。**4b では不採用** (案 A = 時間共有変数の補助変数への吸収を採ったため) |
| `mac_capacity_region_reconciliation` | `MultipleAccess/Reconciliation.lean:292` | 内外を同じ言語に揃える先例 |

**存在しないもの** (Phase 5 の等号が要求し、まだ書かれていないもの): (a) 逆包含
`bcOuterRegionUV W ⊆ martonRegionUnionFS W` (**等号に残る唯一の包含**、在庫 §5-C。旧 (a) の内界側
union は P1–P3 で解消)、(b) more capable の 3 制約を受ける structure (`InBCCapacityRegion` は 2 field)、
(d) `IsBCDegraded W` から `bcConverseAmbient` 上の per-letter Markov 鎖 `h_deg_block` を出す補題
(`bcConverse_deg*` は 0 hit)、(e) `(mutualInfo μ Xs Xs).toReal = entropy μ Xs` と決定的写像の条件付き
エントロピー消失 (semi-deterministic の `H(Y₁)` 用)。旧 (c) 和レート不等式は橋 S5 で解消。
**Mathlib 側の穴はゼロ** (在庫 §6、壁 0 件)。クラス定義そのものは `Classes.lean` で実在化済。

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

### Phase 2 — 補助変数についての union (**Phase 5 の等号の前提**) 🚧

`martonRegion` は `(pV, K)` を引数に取る。真の Marton 内界は補助変数の型と分布についての和集合。
**挟み込み (Phase 3 / 4b) の前提ではない**が、外界が union で内界が四辺形 1 個なので
**等号の前提ではある** (判断ログ 11-(k))。M0 在庫は
[`bc-phase2-union-inventory.md`](bc-phase2-union-inventory.md) (695 行、Mathlib の壁 0 件)。

#### 最小完遂 P1–P3 ✅ (`ce8e9d0b` 在庫 / `fcdafaf5` 実装 / `b1837901` style)

`BroadcastChannel/MartonUnion.lean` (新設、110 行 / 5 宣言)。採った定義:

```
martonRegionUnion W = closure (⋃ k₁ k₂ (pV : Measure (bcAuxAlphabet k₁ × bcAuxAlphabet k₂)) _ K _,
                                 martonRegion pV K W)     -- bcAuxAlphabet k = ULift.{u} (Fin (k+1))
```

設計の 3 点はいずれも**機械確認済**なので蒸し返さないこと: (a) `Fin (k+1)` であって `Fin k` でない
— `k = 0` で `Nonempty` が出ず `martonRegion` のインスタンス要求を満たせない。(b) `ULift.{u}` が要る
— `IsBCLessNoisy` (`Classes.lean:63`) が `∀ (U : Type u)` を量化するので素の `Fin (k+1) : Type 0` は
universe mismatch (在庫 §3 に逐語エラー)。(c) `closure` を外側に取る — 比較先
`bcCapacityRegion` / `bcOuterRegionUV` がともに閉集合で、閉な上位集合は closure を吸収するので
包含に損がない。`@[entry_point]` 2 本 `martonRegionUnion_subset_uv` (**明示仮説ゼロ**) /
`martonRegionUnionFS_subset_capacity` (`hW` のみ) で挟み込みが union の言葉で並んだ。
**ファイル配置は `Marton/` 配下ではなくトップ直下** — `Marton/` は `OuterBoundUV/` を 1 本も import
しておらず (`rg` 実測 0 件)、移すとディレクトリ間依存が双方向になり `docs/rules/module-structure.md`
§5 を破る。トップ直下は family が層をまたぐファイルを置く場所。

⚠ **正直な限界**: この `martonRegionUnion` は**時分割変数を持たない Marton 内界**で、EGK Thm 8.3 の
`⋃ p(q,u,v,x)` 版より一般には真に小さい。

#### 拡張 P4–P7 📋 (詳細と行数見積りは在庫 §12 が SoT)

- [ ] **P4** 非空性 / 下方集合性 (~30 行、`Region.lean` の外界版が雛形)。等号の前提ではない
- [ ] **P5** `Convex ℝ (martonRegion pV K W)` (~20 行、任意)。probe 実測済
- [ ] **P6** 補助アルファベットの付け替え不変性 (~110 行、中核 48 行は probe 実測済)。
      **これが閉じたら L-BCO2 は「答えた」になる**。等号の前提ではない
- [ ] **P7** 全支持の除去 (~180 行、閉じなければ `sorry` +
      `@residual(plan:bc-marton-fullsupport-perturbation)`)。**無制約 union の達成側を言うために要る**
      ⟹ less noisy の等号を `martonRegionUnionFS` で述べるなら不要、`martonRegionUnion` で述べるなら前提

**時分割 / 凸包は要らない** (在庫 §6 が実測で決着、旧 plan の記述を訂正): 各 `martonRegion` は凸
(15 行・測度仮説ゼロ)。union は非凸だが**相手側 `bcOuterRegionUV` も非凸のまま**なので両辺が並ぶ。
時分割変数 `Q` の補助への吸収は Marton では効かない (`I(V₁;V₂)` が `H(Q)` だけ増える) が、less noisy の
2 制約領域では効くので第一目標には不要。**Carathéodory も訂正** — 凸幾何の Carathéodory は
**Mathlib にある** (`Mathlib/Analysis/Convex/Caratheodory.lean:124` / `:149`、loogle 実測)。無いのは
情報理論側の support lemma だけで、濃度固定で止める結論自体は変わらない。
proof-log: no (設計判断は在庫と本節に収まった)。

### Phase 3 — 協調外界 (安い外界) ✅

`e9222d0a` `b9ba272a`。BC 符号を 3 通り (受信機 1 のみ / 受信機 2 のみ / 出力対を 1 出力と見る協調
受信) に還元し、`bcOuterRegionCoop` + `bc_capacity_subset_coop` を得た。単一ユーザー側の入口として
`StrongConverseAsymptotic.lean:805` に `channelCoding_operational_rate_le_capacity` を新設。
**これで `martonRegion ⊆ bcCapacityRegion ⊆ bcOuterRegionCoop` の挟み込みが完成**し、未解決問題の
全景が (緩い外界ながら) Lean に載った。proof-log: no。

### Phase 4a — UV 単一文字化 (floating 形) ✅

`5bf64adf`…`54705cb3`。補助変数を `uvAux` 1 本に統一 (受信機 1 出力の prefix と受信機 2 出力の
suffix を共有し、運ぶメッセージだけが違う) したことで、当初「3 本を同時に扱う」と見積もっていた
identification が 2 本の instantiation に縮んだ。核は新規自作の `csiszar_sum_identity_cond` (既存
`csiszar_sum_identity` の異アルファベット + 背景 conditioner への二重の一般化)。headline
`bc_uv_converse` は **degradedness 前提なし**、構造前提は memoryless 2 本 + encoder Markov 2 本のみ。
proof-log: no (単一文字化の機構は docstring に収まった)。

### Phase 4b — UV 外界の集合化 + 操作的包含 ✅ CLOSED

`6ddb1a48` (実装) / `bfdd55e1` `c768cc00` (両ゲート)。headline
`bc_capacity_subset_uv : bcCapacityRegion W ⊆ bcOuterRegionUV W` (`@[entry_point]`) を**全平面版**で
達成 — 明示仮説は `W` と `[IsMarkovKernel W]` のみ (第一象限制約も符号仮説もなし)。これで
**`martonRegion ⊆ bcCapacityRegion ⊆ bcOuterRegionUV`** が成立し、Phase 3 の
`bcOuterRegionCoop` 版と 2 本並立になった。M0 在庫は
[`bc-uv-operational-inventory.md`](bc-uv-operational-inventory.md) (Mathlib の壁 0 件) で、
S1 共有層 `CodeToAmbient.lean` 新設 → S2 ambient 構成 → S3 構造前提 4 本 (難所 1) → S4 符号レベル
converse → S5 `uvAuxPad` の型統一 (難所 2) → S6 per-letter 同定 → S7 集合化 `IsUVChannelLaw` →
S8-a 平均化 → S8-b 極限 + 退化被覆 (難所 3) を全消化 (`278977c2`…`c768cc00`)。
**L-BCO5 / L-BCO6 いずれも不発動**。宣言の配置は §在庫 が SoT。

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
判断ログ 1 (符号制約を入れない判断が退化被覆を約 15 行に収めた機構) / 11-(f)(g) (MAC 雛形の前提誤り、
「極限を取るだけ」の誤り) / 11 の (e) (`h_ac` が `by_cases` で消えた経緯) / 11-(n) (MAC から読み替えた
橋が degraded 側にはそのままでは効かない) の 4 点。

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

- [x] **前提 = Phase 2 (内界側の union) ✅ 最小完遂**。`martonRegionUnionFS W ⊆ martonRegionUnion W
      ⊆ bcOuterRegionUV W` と `martonRegionUnionFS W ⊆ bcCapacityRegion W ⊆ bcOuterRegionUV W` が
      並んだ ⟹ **等号に残るのは逆包含 1 本** `bcOuterRegionUV W ⊆ martonRegionUnionFS W`
      (在庫 §5-C。これが入れば 4 集合が一斉に等しくなる)
- [x] **内外を同じ添字に載せる橋 (S1–S6) ✅ 全段 proof done** `6b0c1ea1` (在庫) `76b83bc1` `28eae4ea`
      (実装) `0186b708` (style)。M0 在庫は
      [`bc-inner-outer-bridge-inventory.md`](bc-inner-outer-bridge-inventory.md) (Mathlib の壁 0 件)。
      S1 Marton 結合法が `W` のチャネル法 (**入替不要** — `IsUVChannelLaw` は補助 2 スロットを
      ブロックとしてしか見ないので、入替が要るのは情報量スロットを読むときだけ) / S2 入替不変性の
      一般形 / S3 `ℕ` 添字化 + 4 スロット保存 / S4 情報量 3 本の `.toReal` 同定 / **S5 和レート
      不等式** (本命の数学、~257 行。S3 が通った結果 S5 が負うのは `condMutualInfo` 半分だけに縮み、
      需要は `martonInfoₖ - martonInfoV₁V₂ ≤ condMutualInfo` の 2 本) / **S6 順包含
      `marton_region_subset_uv : martonRegion pV K W ⊆ bcOuterRegionUV W` (`@[entry_point]`、~29 行)**。
      配置と宣言は §在庫。両ゲートは honesty が launch 条件外 (新規 sorry / `@residual` ともに 0、
      既存署名の変更なし) + style PASS。**橋は `hpV` / `hK` / `hW` を 1 本も要求しない** (判断ログ 15、
      S5 / S6 でも不変)。予測と実測の差は判断ログ 14 / 16。**逆包含は L-BCO8**
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

proof-log: 定義段と橋 S1–S6 は no (S5 の発見は判断ログ 16 に収まった)。等号が閉じたら yes。

## 後続作業 (Phase 5 の前提ではない)

style / honesty ゲートが提起して当該 leg では見送った項目 + 分割 A の実施後に立った flag。
完了したものは 1 行 + commit に圧縮して残す (項目番号は他文書が参照するので付け替えない)。

### A. `Assembly.lean` の二段分割 ✅ 完了

`210b7558` `e163853d` `69cc5b10` `5c121f95` `3af79fea`。Assembly 1588 → **851 行**、全ファイルが
1500 行ガイド内。汎用ブロックは `Shannon/CondMutualInfoMixture.lean` (新規) / `CodeToAmbient.lean` /
`BroadcastChannel/Basic.lean` へ、領域定義 3 section は `OuterBoundUV/Region.lean` (新規) へ。
**純粋な移設で新しい数学は 0 行 / 新規 sorry 0 / `@audit:ok` は逐語保存**。予測と実測の差は判断ログ 11。

### B. 命名 / 死んだ宣言 (**波及がほぼ 0 の今なら事実上無料**)

1. **`bc_uv_rate_extract` (`Bridge.lean:602`、`@audit:ok`) が dead** — Assembly が
   `bc_uv_converse_slots` に乗り換えた結果、direct consumer **0**
   (`scripts/dep_consumers.sh` 実測)。削除 or 保持の判断が要る
2. **`*_point_mem` 5 本の命名** (`bc_uv_{mixture,shrunk,code,rate,shifted}_point_mem`、`Assembly.lean`
   `:429` / `:565` / `:609` / `:635` / `:696`) — 形容詞が段階を系統的に区別しておらず名前だけでは
   判別不能。`docs/rules/naming.md` §2 は判別子を仮定側に置けと定める (`bc_uv_mem_of_letterSum_le` 等)。
   **波及ほぼ 0** (`bc_uv_shrunk_point_mem` のみ docs 3 本が参照、残り 4 本は Assembly 外ゼロ)
3. `uvAux_pad_mutualInfo_prod_eq` (`Bridge.lean:723`) の `prod` が何の直積か名前から読めない
   (実際は左引数で補助変数と `Xs` を対にする)。`uvAux_pad_pair_mutualInfo_eq` 等へのリネーム提案。
   consumer は in-file 1 件 (`uvAux_pad_condMutualInfo_eq:738`、`dep_consumers.sh` 実測)
4. **命名の軽微な逸脱** `condMutualInfo_eq_of_leftInverse_cond` (`CondMutualInfoMixture.lean:66`) —
   区別子 `_cond` は `_of_` の**前**に置くのが Mathlib 順 (`naming.md` §2)。分割 A の移設は逐語で
   行ったので「移すついでに直す」機会は過ぎた ⟹ 単独のリネーム leg になる。優先度低

### C. 数学的な締めどころ / その他

1. **`bcConverseFanoSlack₁_le` が 2 bit 捨てている** — `Real.log (M₁ - 1) ≤ Real.log M₁` への緩和で、
   `M₁ = 2` では左辺が 0。converse の結論には効かない (余裕は十分) が、将来レートの 2 bit 残差を
   詰めたくなったときの最初の締めどころ
2. `bcOuterRegionUV ⊆ bcOuterRegionCoop` を示せれば「UV は協調外界より狭い」が機械可読になる
   (**任意**。示せなくても挟み込みは 2 本並立で成立する)
3. `CodeToAmbient.lean` の無タグ 7 本 (MAC 由来 6 本 + 分割 A で合流した `le_toReal_of_inv_mul_le`、
   実測)。file 全体のタグ被覆を揃えるなら別 leg。同ファイルに `show` → `change` の linter 警告が
   1 件 (`lake build` でのみ出る)
4. **section 再配置による逐語コピーの完全畳み込み (残 ~30 行)**。
   `∑ i, uvInfo₁ (bcUVJointDistribution c W i)` 形への完全な畳み込みは現配置では不可能 —
   `bcUVJointDistribution` は `uvAuxPad` に依存し、`uvAuxPad` は `bc_uv_converse_from_code` より
   **後ろ**にある。取りに行くなら `section Pad` + `section PerLetterInfo` を `section CodeLevel` の
   **上**へ移す再配置が要る
5. **規約どうしが同じケースで逆方向に引く件 (旧 §F-8 を統合、本 plan の範囲外・記録のみ)**:
   `docs/rules/docstrings.md` item 1 (`## Main statements` 掲載定理には docstring 必須) と
   `scripts/lean_doc_lint.ts` の `internal-doc` ratchet (`:476`) が構造的に衝突する。リンターは
   module doc の Main statements を見ず `@[entry_point]` かタグ持ちだけを headline と見なすので、
   その隙間に落ちた宣言に散文 docstring を足すと 1 本あたり ratchet +1 で `--check` が落ちる。
   **実測**: 分割 A 後に裸 6 本 (`Region.lean` 3 / `CondMutualInfoMixture.lean` 2 / `Assembly.lean` 1)、
   橋 S1–S6 で 4 本 (`martonInfo*_eq_*` 3 本 + `swap_auxiliaries`) が同じ隙間に落ち PostToolUse hook に
   BLOCK された ⟹ **リンターを実装 SoT として裸のままにした**。**分割は衝突を再生産する** (新ファイルの
   module doc が Main statements を書き直すため)。解は「真の headline に `@[entry_point]` を付ける」か
   「module doc の現行慣行を追認する」の二択 = 人の判断で、起票先は `docs/rules/` 側。
   **前者を実践した最初の事例が `Classes.lean`** — Main statements の 4 本すべてに `@[entry_point]` が
   付き、新規 9 宣言で ratchet 寄与 **0**。新規ファイルを切るときの既定手として使える
   (`MartonUnion.lean` もこの手で衝突ゼロ)

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
   決定的な tell: **`Bridge.lean` は本ファイルを `mutualInfo_eq_of_leftInverse` のためだけに import
   しており、mixture 補題を 1 本も使っていない** (参照は `:719` / `:731` の 2 箇所、実測)。分割案 =
   `Shannon/MutualInfoReencoding.lean` (再符号化 3 本) + 現ファイル (mixture 4 本、前者を import)。
   consumer が既に綺麗に分かれている (Bridge → 再符号化のみ / Assembly → 両方) ので循環なし。
   **193 行で行数圧力はゼロ**だが consumer が 2 ファイルの今が最も安い。着手時は判断ログ 11-(i) を
   先に適用すること (import は consumer 表ではなく**移動先が引かざるを得ない依存の閉包**で決まる)
2. **`open scoped BigOperators` が tree 全体で死んでいる** — 今の Mathlib では `∑`/`∏` 記法が
   global。style ゲートが `Region.lean` から外して EXIT=0 を確認したが、同じ open を持つファイルが
   **189 本** (実測) あり数ファイルだけ外すと不揃いになるので戻した。tree 一括 sweep
   (一括置換 + `lake build` 1 回) として別 leg にするのが筋で、BC 固有ではないので**本 plan の
   範囲外** (起票先は `docs/rules/` 側)

### F. Phase 5 (定義段 + 橋 S1–S6) と Phase 2 (P1–P3) が新たに立てた flag

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
   弱く、等号が閉じた段で登録するのが自然。`docs/readme-theorems.txt` は未編集。
   **判断待ち (S6 で発生)**: `marton_region_subset_uv` は等号ではないが `bc_capacity_subset_uv` と
   対になる強さの `@[entry_point]` ⟹ **等号を待たず橋の段で登録してよいか**を決める必要がある
6. **リネーム束 — 4 本まとめて 1 leg (旧 F-6 / F-7 + `martonInfoSum` + `FS` 略記)**。いずれも
   **外部 consumer 0** (`rg` 実測) = 今が最安。前 3 本は参照が `MartonBridge.lean` 内で閉じている:
   - `auxNatIndex` → `natIndex` (推奨度 中) — 定義は `Fintype.equivFin X x` で任意の `Fintype X` に
     総称であり、「補助変数の」は使用側のラベルにすぎない。加えて Mathlib 慣行の `aux` = 繋ぎ宣言と
     読めるので `docs/rules/naming.md` の proof-staging 語彙の隣に落ちる
   - `martonSwapLaw` → `martonAuxSwapLaw` (推奨度 低) — 何を swap したのかが名前に出ていない
   - **`martonInfoSum` が実在しない識別子** (推奨度 低) — `martonInfoSum_le_uvInfoSum₂_toReal:493` /
     `…₁_toReal:509` の左辺は def として存在せず、実体は `martonInfo₁ + martonInfo₂ -
     martonInfoV₁V₂` のベタ書き (= `InMartonRegion` の第 3 制約) ⟹ 読者が grep して空振りする。
     解消は (a) `Marton/Setup.lean` の `martonInfo₁:244` / `martonInfoV₁V₂:262` の隣に
     `def martonInfoSum` を新設して使う、(b) リネーム、の二択。**新規 public 5 本は外部 consumer 0**
   - **`FS` 略記 → `FullSupport`** (推奨度 高、Phase 2 の style 監査が提起、**未実行**) —
     `martonRegionUnionFS` / `_FS_subset_union` / `_FS_subset_capacity` の 3 本。`rg` 実測で `FS` を
     宣言名断片に使うのは tree 全体でこの 3 本のみ (**先例ゼロ**)、in-repo の綴りは展開形だけ
     (`IsHoeffdingMinimizerFullSupport` 等)。`docs/rules/naming.md` の認容略語表は `pos/neg/nonpos/
     nonneg` 系のみで、`FS` は情報理論の慣用略語でもない。**Phase 5 が消費し始める前の今が最安**

   **束に入れない判定が 2 件**(蒸し返し防止): (a) **`bcAuxAlphabet` は `auxNatIndex` とは別の束** —
   ここでの `Aux` は Mathlib 慣行の「繋ぎ宣言」ではなく**教科書用語の auxiliary random variable** で、
   同族の descriptive 先例が 4 本 (`uvAux` / `martonAux₁₂` / `uvAuxPad` / `uvAuxCopiesOutputLaw`)。
   弁別軸は「総称なのに補助を名乗る (over-claim)」か「補助としてしか使われない」か。
   (b) **`martonRegionUnion_subset_uv` は family 既定と食い違っていない — 逆に既存 2 本が outlier** —
   `naming.md` は head symbol の casing を保つ形で、family の他 (`martonJointDistribution_isUVChannelLaw`
   / `martonInfo₁_eq_uvInfo₁_toReal` / `bcOuterRegionUV_isClosed`) はそうなっている。
   `marton_region_subset_uv` / `marton_region_subset_capacity` だけが def 名を割っていて
   **def 名で grep すると引っかからない**。統一するなら直すのは古い 2 本だが、両方 `@[entry_point]` +
   `@audit:ok` で実 consumer あり ⟹ `dep_consumers.sh` + README 定理表の確認が要る別 leg。優先度低
7. (旧項目は F-6 のリネーム束に統合)
8. (**§C-5 に統合**) 規約衝突は BC 固有ではなくツリー全体のギャップ。安い手は
   `martonInfo*_eq_*` 3 本への `@[entry_point]` 付与だが headline 認定の判断なので未着手
9. **`docs/rules/lean-style.md:29` が repo 実態と矛盾** (橋 S5 / S6 の style ゲートが提起、
   **本 plan の範囲外・記録のみ**) — 「演算子は行末に置いて改行する (次行頭に演算子を置かない)」は
   複数行シグネチャの**関係記号**には当てはまっていない。継続行を関係記号で始める行は tree 全体で
   **約 5800 行 / 353 ファイル** (実測)。実態に合わせるなら「項レベルの算術演算子に限る」と scope
   するか、複数行 statement では関係記号を継続行頭に置く形を明示的に許すのが筋。起票先は
   `docs/rules/` 側で、`docs/rules/` の編集自体は本 leg で行っていない

以下 3 件は橋 S5 / S6 の style ゲートが提起し、**いずれも未実行**。

- **F-a: `isMarkovChain_map_comp` (`MartonBridge.lean:264`、private、15 行) を
  `ChannelCoding/CodeToAmbient.lean` の `### Information transport under a shared pushforward` 節
  (`:430`–`:520`) へ上流移動** — 同節の `mutualInfo_map_comp:435` / `condDistrib_map_comp:448` /
  `condMutualInfo_map_comp:465` / `condMutualInfo_map_comp':499` と名前の形・型変数レイアウト・
  引数順が完全に同族で、同節の `condDistrib_map_comp` を直接消費している。**import 書換ゼロ**
  (`CodeToAmbient` は既に import closure 内)。移動時は binder 名 `Xs / Zc / Yo` を family の
  `f / g / h` に揃える。⚠️ 移動先で docstring を付けると `internal-doc` ratchet が +1 になるので、
  bare のままにするか baseline を上げるかの判断が要る (§F-8 と同一の軸)
- **F-b: `mutualInfo_le_add_condMutualInfo` (`MartonBridge.lean:357`、private、8 行、
  `I(A;C) ≤ I(A;B) + I(A;C|B)`) を `Shannon/CondMutualInfo.lean` へ上流移動** — BC 固有要素ゼロの
  教科書的不等式で、依存 4 本すべてが移動先で可視ゆえ **import 書換ゼロ**。**条件付き版
  `condMutualInfo_le_add_condMutualInfo` が `OuterBoundUV/Gateway.lean:194` に public + `@audit:ok`
  で既存**なので、無条件版が private で 2 ファイル離れて埋まっている状態は「既に書いたか」失敗
  モードの温床。結論形検索で tree 全体の重複は本件 1 件のみ (既存重複なし)
- **F-d: public / private の非対称 (API 面、人の判断待ち)** — `martonInfoV₁V₂_eq_mutualInfo_toReal:252`
  は public かつ `## Main statements` 掲載なのに、完全な兄弟 `martonInfo₁_eq_mutualInfo_toReal:403` /
  `martonInfo₂_eq_mutualInfo_toReal:414` は private。3 本とも API にするか V₁V₂ 版だけにするかが
  意図的な線引きに見えない

## 未解決本体との距離 (正直な見積り)

「Marton 内界 = 一般 BC の容量領域か」は **open**。数学が存在しないので形式化できない。本計画が
終わっても未解決問題は未解決のままで、得られるのは以下。

- 内界・外界・容量領域が同一言語で並び、**ギャップが機械可読な形で固定される**
- 特定の BC で内外が分離するかを検証する基盤 (反例候補の検算)
- 一致が既知の特殊クラスについては、等号が実際に閉じる (Phase 5)

期待値は「厳密な足場 + 教材価値」に置くのが妥当。形式化が情報理論の未解決問題の解決に直接
寄与した前例は無い、という前提で計画している。

## 設計上の未決事項

1. **補助変数 union の射程** (Phase 2) — **濃度固定で止める形で決着** (P1–P3)。情報理論側の
   Carathéodory (support lemma) は書かない。残る判断は P7 (全支持の除去) を等号の前に取るか
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
| **L-BCO2** | Phase 2 の型量化 union が universe 問題で詰む | 濃度固定版で止め、union は取らない。**「Phase 3–5 は影響を受けない」は誤りだったので撤回** — 影響を受けないのは Phase 3 / 4 (挟み込み) だけで、**Phase 5 の等号は union を前提とする** (判断ログ 11-(k))。この撤退を取ると等号は「∃ pV K」形の弱い主張に落ちる。**不発動 (P1–P3、在庫 §3 が機械確認)。ただし旧記述「実質的に前倒しで解けている公算」は半分誤りだった** — 問題は union の**定義側ではなく消費側**にあり、本体は `IsBCLessNoisy` (`Classes.lean:63`) が `U : Type u` を量化していること。採用した `bcAuxAlphabet = ULift.{u} (Fin (k+1))` はこれを **0 行で吸収**する (在庫の probe が `hln (bcAuxAlphabet.{u} k) pU K` を機械確認) ⟹ 旧 plan が要求していた「ULift probe の書き下し直し」は**不要になった**。**「解けた」でも単なる「回避」でもない**: 濃度固定の案は型量化を持たないので発動条件に到達しない (定義側では回避) が、消費側で同じ問題が出るのを `ULift` が吸収した、という位置づけ。**P6 (付け替え不変性) が閉じたら「答えた」になる** |
| **L-BCO3** | Phase 5 の等号が Phase 4 の外界の形と噛み合わない | クラス定義だけ入れて等号は defer。**発動条件の文言は実態とずれている** (在庫 §7): 噛み合わなさの本体は外界の形ではなく**内界の形** (符号制約 = `2c938fe0` で解消 / union なし = Phase 2 / 全支持仮説 = L-BCO7) だった。slug は凍結なので文言はそのまま残し、判定は内界側の 3 点で行う |
| **L-BCO4** | Phase 4b の符号→ambient 橋または単一文字還元が閉じない | **不発動のまま Phase 4b が完遂** — 橋は S1–S4、集合化は S7、平均化は S8-a、極限と包含は S8-b でいずれも closure した |
| **L-BCO5** | S5 の補助変数の型統一が `mutualInfo_chain_rule` 経由でも閉じない | **不発動** — 在庫の攻略路 (両向き DPI + `mutualInfo_chain_rule` + `ENNReal.add_right_inj`) がそのまま効いた。退避先だった「`n` を露出した族 `bcOuterRegionUVAt W n` + `⋂ n` 版」は採らない (slug は他文書参照のため凍結) |
| **L-BCO6** | S8-b の退化レート被覆が MAC 同様 450 行級に膨らむ | **不発動** — 退避先だった第一象限交差版は採らず、`bc_capacity_subset_uv` は**全平面版**で closure した (退化被覆の実測は約 15 行 + `2 ≤ M` の穴埋め 55 行、判断ログ 1) |
| **L-BCO7** | semi-deterministic の等号を狙う段で、`marton_achievability` の全支持仮説 `hW` が外せない (判断ログ 13) | **semi-deterministic はクラス定義 + 外界側だけで止め、等号は述べない**。外界 (`bc_capacity_subset_uv` の特殊化) は `hW` を要求しないので単独で成立する。退避の出口は `sorry` + `@residual(plan:bc-semideterministic-fullsupport)` (= `hW` を外す後継 plan のファイル名 stem)。**`IsSemiDeterministicAchievable` のような述語に核を束ねる形は取らない**。**橋は本ラインの外**: 橋 S1–S6 は `hpV` / `hK` / `hW` を 1 本も要求しない (判断ログ 15) ので semi-deterministic チャネルでも成立する ⟹ L-BCO7 が止めているのは内界の**達成側** `marton_achievability` だけで、発動判定はその 1 点で行う |
| **L-BCO8** | 等号の逆包含 (`bcOuterRegionUV W ⊆ martonRegionUnionFS W`) を書く段で、`bcOuterRegionUV` の `ℕ` 補助を `martonInfo*` の `[Fintype]` 要求に合わせられない (Carathéodory 型の濃度上界が要る)。**発動条件の形が変わった (P1–P3、在庫 §4-C が機械確認)** — 濃度固定により **`Fintype ℕ` 閉塞は解消**し、前 leg の逐語エラー `failed to synthesize instance of type class Fintype ℕ` は**再現しない**。⟹ **型では塞がらず、残るのは数学**: (i) Carathéodory 型の濃度上界、または (ii) `ℕ` 補助の有限量子化 + 内界 union の `closure` による極限回収。**内界が closure である以上 (ii) は構造的に可能な形**で、前 leg には無かった選択肢。(i)(ii) とも未検証 (confidence = human-judgment) ⟹ **発動判定は Phase 5 (等号) へ持ち越し** | **順包含側だけで止める** (橋 S6 = `marton_region_subset_uv` `28eae4ea` + `martonRegionUnion_subset_uv` `fcdafaf5` で成立済)。逆包含は `sorry` + `@residual(plan:bc-marton-uv-cardinality-bound)` で**署名を保つ**。**退避前に 1 度試す代替**: `martonInfo*` を `ℝ≥0∞` の `mutualInfo` / `condMutualInfo` 版に置き換える定義 pivot。ただし `marton_achievability` (`Marton/Achievability.lean:767`) が `martonInfo*` を仮説に持つので `scripts/dep_consumers.sh` の実測が先。**`IsMartonCoverable` のような述語に「逆包含が成り立つ」を束ねる形は取らない** |

**active な撤退ラインは L-BCO2 / L-BCO3 / L-BCO7 / L-BCO8 の 4 本** (Phase 2 用 1 本 + Phase 5 用 3 本)。

**禁止事項**: どの撤退でも「外界が成立する」「補助変数が取れる」「符号から ambient が取れる」等を
`*Hypothesis` 述語に束ねて仮説として渡す形は取らない (CLAUDE.md 検証の誠実性 tier 5)。退避は
`sorry` + `@residual` で、署名は証明したい形のまま保つ。Phase 5 で等号を述べる段では、クラス条件
(less noisy 等) を「等号が成り立つ」に近い形の述語で受け取っていないかを毎回確認する。

## 推奨実行順

定義段 → 橋 → Phase 2 の最小完遂まで到達した。**残るは等号 1 本**:

```
Phase 5 定義段 ✅ → 内外の橋 S1–S6 ✅ (Marton 法を ℕ 添字に載せ、順包含 marton_region_subset_uv まで)
  ↓
Phase 2 最小完遂 P1–P3 ✅ (martonRegionUnion / …FS + @[entry_point] 2 本)
  ↓
less noisy の等号  ← ★次の一手。残る包含は bcOuterRegionUV ⊆ martonRegionUnionFS の 1 本 (在庫 §5-C)
  ↓                  (詰んだら L-BCO8 — 型では塞がらず、残るのは濃度上界 or 有限量子化 + 極限回収)
more capable の等号 (3 field の新 structure) → semi-deterministic は L-BCO7
```

**P4–P7 は等号の前提か**: P4 / P5 / P6 は前提ではない (API の完全性と L-BCO2 の完答)。**P7 (全支持の
除去) だけは等号の述べ方で決まる** — `martonRegionUnionFS` で等号を述べるなら不要、無制約
`martonRegionUnion` の達成側を言うなら前提。less noisy がどちらを要求するかで優先度が決まる。
§後続作業 B–F はいずれも前提ではない (F-1 / F-6 リネーム束 / F-10 のみ consumer が 0 の今が最安)。

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
    S8-b までの 5 件 (a)–(e): 一般化の方向が 1 段広かった (S3) / `macConverseInput_eq` = `absent` は
    誤り (S4) / union 無制約化の反例 class が在庫に無かった (S6→S7、判断ログ 9) / 0-hit 見落とし /
    在庫が名指しした危険 `h_ac` が `by_cases` の否定側で **∞ = ∞** に落ちて丸ごと消えた
    (S8-a、over-estimation 側)。分割 A の 3 件 (h)–(j) は**すべてファイル境界の読み違い**:
    consumer 表は移す decl 全部を行にする / **import の必要性は consumer 表ではなく移動先の依存の
    閉包で決まる** / 移設は移動元の import を殺す (実測 4 本)。生きた教訓は以下:
    - **(f) 雛形を参照するときは「その雛形の到達目標が自分と同じ強さか」を先に確認する** —
      「MAC の約 420 行が退化レート被覆の雛形」は誤りで、MAC はそもそも退化レートを被覆していない
      (`mac_timesharing_capacity_region` 自身が第一象限交差版 = 最初から L-BCO6 相当)。
    - **(g) 前 step の到達点が次 step の入口として使えるとは限らない** — 縮小点の**加法形**は極限に
      乗らない (`BCAchievable` は `M₂` を下からしか縛らず `Real.log M₂` が非有界)。**乗法形**
      (`bc_uv_code_point_mem`) への差し替えで解決。step 境界では結論の**形**を独立に確認する。
    - **(k) 「独立」「park 可」の判定は到達目標ごとに違う** — Phase 2 は挟み込みの前提ではないが
      **等号の前提**だった (外界は union、内界は四辺形 1 個)。park 判定は目標を名指して書く。
    - **(l) more capable は「単純化」ではなく「形が違う」+ 文献帰属が 1 件誤り** — less noisy は
      **Körner–Marton 1975/1977** (El Gamal 1979 は more capable)。制約は 4 → 3 に減るのに
      `R₁ + R₂ ≤ I(X;Y₁)` が補助変数を含まない新形ゆえ受け皿の structure は新設が要る。
    - **(m) `.toReal` の危険の向きが逆だった** — `⊤ ↦ 0` は外界を**縮める**ので逆包含では保護側。
      危険は無限アルファベット拡張の 1 軸だけ。⟹ 「非対称性がある」で止めず**どちらの向きに
      倒れるかまで言い切る**。⚠ **この判定は外界についてのみ正しい** — 内界を `ℕ` 補助に載せると
      `I(V₁;V₂) = ⊤ ↦ 0` が罰則項を消して順包含ごと偽になる (判断ログ 17)。
    - **(n) 「同じ floating 形だから橋が効く」は形の一致であって仮説の一致ではない** —
      `bc_converse` の degradedness は `IsBCDegraded` ではなく `h_deg_block` (ambient 上の
      per-letter Markov 鎖) で、`bcConverse_*` 対応版は 0 hit、新規 ~120 行が要る。
      再利用可否は結論形ではなく**要求される仮説の表現**で決まる。
    - **(o)/(p)** more capable の定義に要る `Kernel.fst/snd W` は `bcOuterRegionCoop` で使用済だった /
      `bc_converse` / `bc_achievability` は direct consumer 0 件ゆえ「接続」ではなく「新規実装」で
      見積る (`dep_consumers.sh` 実測)。
12. **片側で採った規約変更は、対になるもう片側にも適用したか確認する (P1、`2c938fe0` で解消)**:
    判断ログ 1 の「外界に第一象限制約を入れない」判断を**内界に適用する step が無かった** —
    `martonRegion` だけが第一象限のまま残り、`bcOuterRegionUV ⊆ martonRegion` は**どの `W` でも偽**
    だった (在庫が `(-1,-1)` で機械確認)。気づかずに等号へ着手すれば全チャネルで偽の目標を追っていた。
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
14. **「内外の橋は `.toReal` の同定 1 本のみ」は 3/4 だけ正しかった (橋 S1–S6)**: 3 スロットには
    1 本 6 行で足りるが、**和レート制約には対応物が存在しない** (内界は `I₁+I₂-I₁₂` 1 本、外界は
    `uvInfoSum₂` / `uvInfoSum₁` の 2 本で別の汎関数) ⟹ 情報量不等式の自作 (S5) が要った。
    **行数の予測 → 実測**: S1 50→45 / S2 30→22 / S3 40→95 / S4 25→35 / S5 150–250→257 / S6 40→29
    (超過は数学ではなく**署名の反復** = 型クラス束が 8 宣言に付く。証明本体は 2–5 行)。
    ⟹ 一般教訓: **「同定 1 本で済む」の見積りは、内外の制約が同数・同形かを先に数えてから立てる**。
    本数が違う (内界 3 本 vs 外界 4 本) 時点で、余った 1 本が別の数学であることは確定していた。
15. **橋は内界側の全支持仮説を 1 本も要求しない ⟹ L-BCO7 は緩む方向 (S1–S6 を通じて不変)**:
    明示仮説は `pV` / `K` / `W` と `[IsProbabilityMeasure pV] [IsMarkovKernel K] [IsMarkovKernel W]`
    だけで、`hpV` / `hK` / `hW` は 1 本も現れない (S6 まで署名走査で実測)。⟹ **semi-deterministic
    チャネルでも橋は成立する**。L-BCO7 が止めているのは内界の**達成側**であって橋ではない。
    ⟹ 一般教訓: **撤退ラインは「どの宣言が止まるか」まで降ろして書く**。「クラス X では内界が
    使えない」の粒度だと、実際には無関係な後続 step まで巻き込んで park することになる。
16. **在庫が予告した攻略路が丸ごと不要になった (橋 S5、予測の外れ 3 件)**: (a) 「条件付き DPI は
    in-project に無いので 5 step で挟む」は誤りで `condMutualInfo_le_of_markov_joint`
    (`ChannelCoding/ConverseMemorylessChainRule.lean:113`) が要求どおりの形で存在し、核は **8 行 × 2**
    に縮んだ / (b) ブリーフが名指した `Marton/MarkovCore.lean` は**宣言 0 本** (効いたのは
    `CodeToAmbient.lean:71`) / (c) 当てたのは**名前検索**で、結論形検索では conditional 版が出なかった。
    ⟹ 一般教訓: **在庫が「無いので自作する」と書いた資産は、実装着手時に両方の検索軸で引き直す** —
    在庫段階の 0-hit は検索軸に依存し、CLAUDE.md が推す結論形検索だけでは構造的に見えない資産がある。
17. **内界を `ℕ` 補助に載せる設計は反例で潰れた (Phase 2、在庫が機械確認)**: 外界と同じ `ℕ` 添字の
    5 つ組法に内界も載せれば橋が要らなくなる、という設計 (ブリーフが誘導していた形) は**順包含が
    偽になる**。反例は `W a = dirac (a, a)` で、`H(N) = ∞` の `N` を `X` と一緒に両補助へ詰めると
    `I(V₁;V₂) = ⊤ ⟹ .toReal = 0` で和レートの罰則項が消え、`|α| = 2` のとき点 `(log 2, log 2)` が
    内界に入る (合計容量は 1 bit なので内界ですらない)。**構造的理由**: 外界の 4 スロットは全部
    **出力との**情報量なので有限出力なら自動的に有限だが、**内界の `I(V₁;V₂)` だけが補助 × 補助**。
    ⟹ 判断ログ 11-(m) の「`.toReal` の危険は無限アルファベット拡張の 1 軸だけ」は**外界についてのみ
    正しく、内界を `ℕ` に載せた瞬間に発火する**。採用した濃度固定 (`Fin (k+1)`) はこの反例 class を
    型で閉じている。⟹ 一般教訓: **同じ変換 (`.toReal`) の安全性は、それが載る汎関数の引数がどこから
    来るかで決まる**。「片側で安全と判定した規約を対辺にも適用してよいか」は判断ログ 12 と同じ軸。
