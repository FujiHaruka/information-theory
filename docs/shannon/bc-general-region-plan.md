# Shannon: 一般 BC 容量領域フレーム サブ計画

> **Parent**: [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md) §L-BC5 後続

未解決問題「一般 2 受信者 BC の容量領域の特徴づけ」に対して形式化が提供できるのは **足場**
(内界 / 外界 / 両者による挟み込み) までで、未解決本体 (内外一致) は数学が存在しないので Phase 外。
本計画はその足場を組む。到達目標は `martonRegion W ⊆ bcCapacityRegion W ⊆ bcOuterRegion W` を
Lean の 1 本の定理列として持つこと。

## 進捗

- [x] Phase 1 操作的容量領域 (主語) ✅ `fd39ad95` `deb930a7`
- [ ] Phase 2 補助変数 union (独立・park 可) 📋
- [x] Phase 3 協調外界 (安い外界) ✅ `e9222d0a` `b9ba272a`
- [x] Phase 4a UV 単一文字化 (floating 形) ✅ `5bf64adf` `f7023332` `bff554c2` `33ec3522` `54705cb3`
- [x] Phase 4b UV 外界の集合化 + 操作的包含 ✅ `6ddb1a48` `bfdd55e1` `c768cc00` (**全平面版**)
- [ ] Phase 5 一致クラスの拡張 🚧 ★現在の本線

## 在庫

| 資産 | 場所 | 用途 |
|---|---|---|
| `BCAchievable` / `bcCapacityRegion` | `BroadcastChannel/Operational.lean:53` / `:68` | 主語。Phase 3/4b の包含の左辺 |
| `bc_capacityRegion_isClosed` / `bc_achievable_mono` / `bc_mem_closure_of_strictly_below` | `Operational.lean:102` / `:71` / `:86` | 閉性・down-set 性・厳密不等号からの closure 回収 |
| `martonRegion` / `marton_region_subset_capacity` | `Operational.lean:121` / `:149` | 内界の集合版と包含 (`@[entry_point]`) |
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
| `MACAchievable` / `macPentagon` / `macCapacityRegion` | `MultipleAccess/TimeSharing.lean:49` / `:58` / `:66` | 操作的述語 → closure で集合化のパターン |
| **MAC の符号→ambient 橋** | `MultipleAccess/TimeSharingConverse/Bridge.lean` (847 行 / 37 decl) | **S6 の雛形 (消化済)**。per-letter 同定は `macConverse_map_triple_eq:718` → 同定 3 本 `:771` / `:797` / `:823` |
| **MAC の集合化 + 極限** | `MultipleAccess/TimeSharingConverse/Assembly.lean` (953 行 / 12 decl) | S8-a までの雛形。`bc_capacity_subset_uv` の対応物は `mac_timesharing_converse:817` / `mac_timesharing_capacity_region:908` — ただし後者は**第一象限交差版**で、MAC はそもそも退化レートを被覆していない (判断ログ 11-a)。`:397`–`:817` の約 420 行は「軸上の点」用であって退化被覆の一般解ではなく、**S8-b では不採用** |
| `mac_avgPentagon_mem_convexHull` | `TimeSharingConverse/Bridge.lean:99` | n 文字平均を単一文字分布の凸包へ落とす先例。**4b では不採用** (案 A = 時間共有変数の補助変数への吸収を採ったため) |
| `mac_capacity_region_reconciliation` | `MultipleAccess/Reconciliation.lean:292` | 内外を同じ言語に揃える先例 |

**存在しないもの**: less noisy / more capable / semi-deterministic のクラス定義
(project 全体で 0 hit) = Phase 5 の入口。Phase 4b が要求した資産は S1–S8-b で全部実在化した。

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
なお degraded 版 `bc_converse` も floating 形で止まっているので、4b の橋は degraded 側にも効く
共有資産になる。

## Phase 詳細

### Phase 1 — 主語を作る (操作的容量領域) ✅

`fd39ad95` `deb930a7`。`BCAchievable` / `bcCapacityRegion := closure {…}` / `martonRegion` を定義し、
`marton_region_subset_capacity` で内界を集合の言葉に載せた。副産物として `marton_achievability`
から使われていない正値仮説 2 本を除去 (定理が強くなる方向、consumer 0 件)。
proof-log: no (MAC の写経で設計判断が無かったため)。

### Phase 2 — 補助変数についての union (独立、park 可) 📋

`martonRegion` は `(pV, K)` を引数に取る。真の Marton 内界は補助変数の型と分布についての和集合。

- [ ] 型量化の回避: `V₁ V₂ : Type*` の量化は universe 問題を生むので、濃度を `Fin k` に固定して
      `k` について union する形を採る
- [ ] Carathéodory 型の濃度上界 (補助変数のアルファベットを入力アルファベットで抑える) は
      Mathlib にも in-repo にも無い。**自作コストが読めないので、濃度固定版で止めるのが honest**
- [ ] time-sharing / convex hull が要るなら `MultipleAccess/TimeSharingConverse/` の資産を参照

**Phase 3–5 の前提ではない**。挟み込みだけなら Phase 1 の点ごとの形で言える。
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
(d) 橋 (S1–S4) は degraded 側 `bc_converse` にも効く共有資産なので、MAC からの読み替えで
何が効かなかったかを残す価値がある。

### Phase 5 — 一致するクラスを広げる 🚧 ★本線

degraded は既に閉じている。その一般化を、Phase 1 の内界と Phase 4b の外界の組で回収する。
**Phase 4b が前提だったのは満たされた** — 内界も外界も集合の言葉に載ったので `martonRegion` と
`bcOuterRegionUV` を直接並べられる。

- [ ] クラス定義の新設 (project に 0 hit): more capable / less noisy / semi-deterministic
      — 等号を述べる前でも定義と基本性質は入る。ここから着手するのが安い
- [ ] **semi-deterministic BC** (Marton 1979) — Marton 内界 = 容量領域が既知
- [ ] more capable / less noisy — 外界が UV より単純な形を取る (El Gamal 1979)
- [ ] degraded を新クラスの特殊化として既存 `bc_converse` / `bc_achievability` に接続。
      `bc_converse` 自身も floating 形なので、ここでも 4b の橋 (S1–S4) が効く
- [ ] **着手前に 1 度確認すること (S8-a / S8-b の honesty 監査 2 回分からの引き継ぎ)**:
      `uvRegion` の 4 制約は `ℝ≥0∞` の `.toReal` を通るため、情報量が `⊤` になる状況では制約が
      `≤ 0` に**強化**される = 領域が**狭くなる**側に倒れる。
      - **有限アルファベットでは `⊤` は起きないので現状は無害**。外界 (converse) 方向では主張を
        強める側なので安全でもある
      - **逆向きに効く軸が 2 つある**: (i) 逆包含 (achievability / 領域 ⊆ operational) を証明する段、
        (ii) `StandardBorelSpace` 側 (無限アルファベット) への拡張。後者では外界が不当に狭くなって
        converse が偽になりうる。どちらかに進むなら `.toReal` を取る前の `ℝ≥0∞` 版制約への
        移行を検討する価値がある

proof-log: 未定 (クラス定義段は no、等号が閉じたら yes)。

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
   = **本 plan の範囲外** (`docs/rules/` 側の課題として起票)

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

## 未解決本体との距離 (正直な見積り)

「Marton 内界 = 一般 BC の容量領域か」は **open**。数学が存在しないので形式化できない。本計画が
終わっても未解決問題は未解決のままで、得られるのは以下。

- 内界・外界・容量領域が同一言語で並び、**ギャップが機械可読な形で固定される**
- 特定の BC で内外が分離するかを検証する基盤 (反例候補の検算)
- 一致が既知の特殊クラスについては、等号が実際に閉じる (Phase 5)

期待値は「厳密な足場 + 教材価値」に置くのが妥当。形式化が情報理論の未解決問題の解決に直接
寄与した前例は無い、という前提で計画している。

## 設計上の未決事項

1. **補助変数 union の射程** (Phase 2) — 濃度固定で止めるか Carathéodory を自作するか
2. **`uvRegion` の `.toReal` を `ℝ≥0∞` 版に移すか** (Phase 5、無限アルファベット拡張の前) →
   Phase 5 の最終チェック項目

Phase 4b の 2 件 (単一文字還元の形 / 結合 memoryless の持ち方) は決着済 (案 A 採用 / 構成側で
持つ、S3 で機械確認)。履歴は git。

## 撤退ライン (frozen slug)

| slug | 発動条件 | 退避先 |
|---|---|---|
| **L-BCO1** | Phase 4 の補助変数 identification が閉じない | **不発動** — Phase 4a で `uvAux` 1 本の 2 通り instantiation により閉じたため、Körner–Marton / Sato への後退は不要になった |
| **L-BCO2** | Phase 2 の型量化 union が universe 問題で詰む | 濃度固定版で止め、union は取らない (Phase 3–5 は影響を受けない) |
| **L-BCO3** | Phase 5 の等号が Phase 4 の外界の形と噛み合わない | クラス定義だけ入れて等号は defer |
| **L-BCO4** | Phase 4b の符号→ambient 橋または単一文字還元が閉じない | **不発動のまま Phase 4b が完遂** — 橋は S1–S4、集合化は S7、平均化は S8-a、極限と包含は S8-b でいずれも closure した |
| **L-BCO5** | S5 の補助変数の型統一が `mutualInfo_chain_rule` 経由でも閉じない | **不発動** — 在庫の攻略路 (両向き DPI + `mutualInfo_chain_rule` + `ENNReal.add_right_inj`) がそのまま効いた。退避先だった「`n` を露出した族 `bcOuterRegionUVAt W n` + `⋂ n` 版」は採らない (slug は他文書参照のため凍結) |
| **L-BCO6** | S8-b の退化レート被覆が MAC 同様 450 行級に膨らむ | **不発動** — 退避先だった第一象限交差版は採らず、`bc_capacity_subset_uv` は**全平面版**で closure した (退化被覆の実測は約 15 行 + `2 ≤ M` の穴埋め 55 行、判断ログ 1) |

**active な撤退ラインは L-BCO2 / L-BCO3 の 2 本のみ** (どちらも Phase 2 / Phase 5 用)。

**禁止事項**: どの撤退でも「外界が成立する」「補助変数が取れる」「符号から ambient が取れる」等を
`*Hypothesis` 述語に束ねて仮説として渡す形は取らない (CLAUDE.md 検証の誠実性 tier 5)。退避は
`sorry` + `@residual` で、署名は証明したい形のまま保つ。Phase 5 で等号を述べる段では、クラス条件
(less noisy 等) を「等号が成り立つ」に近い形の述語で受け取っていないかを毎回確認する。

## 推奨実行順

**次の本線は Phase 5 (クラス定義 → 等号)**。分割 A が済んで `Assembly.lean` に 650 行の余裕が
できたので、着手を阻む前提は残っていない。Phase 2 は独立で、いつ入れてもよいし入れなくても本線は
完結する。§後続作業 B–E はいずれも Phase 5 の前提ではない。

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
11. **在庫予測の外れ (通算 10 件) — 在庫ファイル自体は編集しないので本エントリが記録の SoT**。
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
    - **(h) consumer 実測表が 1 本落ちていた**: §後続作業 A の表は `mutualInfo_eq_of_leftInverse` と
      `compProd_pi_map_pair_eq_of_update_invariant` の 2 本しか載せず、**同じ leg で移す
      `compProd_comap_map_prodMap` を落としていた**。実測 consumer は 2 decl
      (`IsUVChannelLaw.map_auxiliaries` / `IsUVChannelLaw.map_input_output`) で、どちらも
      `section ChannelLaw` = **二段目で `Region.lean` へ移る側**。結果は無害 (推移的に届いた) だが、
      表の目的 (移動先を import する必要がある側を漏らさない) に対して穴が開いていた。
      ⟹ consumer 表は**移す decl 全部**を行にする。1 本でも欠けると表が「網羅」の役を果たさない。
    - **(i) 「新ファイルなので import が要る」という予測が誤り**: (h) から立てた予測
      「`Region.lean` は `CodeToAmbient` を明示 import する必要がある」は外れた。`Region.lean` は
      `uvRegion` が使う `uvInfo₁/₂` のために `Bridge.lean` を import せざるを得ず、その `Bridge` が
      既に `CodeToAmbient` を import している ⟹ 推移的に自動で届く。明示 import は入れたが
      **コンパイル上は必須ではなく規律上望ましいだけ**だった。
      ⟹ 一般教訓: **import の必要性は consumer 表では決まらない**。決めるのは
      **移動先ファイルが他に何を import せざるを得ないかの閉包**なので、判断はそちらを見てから行う。
    - **(j) 移設は移動元の import を殺す**: plan は「移設で死ぬ import」を予測していなかったが、
      実測で 4 本 (うち Mathlib 2 本) が dead になった (`69cc5b10`)。宣言が抜ければその宣言だけが
      使っていた import が浮くのは**規則的に起きる**。
      ⟹ 移設 leg には最初から「移動元の import 生死を実測する」step を入れる。
