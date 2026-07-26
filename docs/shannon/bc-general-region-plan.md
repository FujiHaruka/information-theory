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
- [ ] Phase 4b UV 外界の集合化 + 操作的包含 🚧 ★現在の本線 (M0 在庫 ✅ / S1–S7 ✅ / S8-a ✅ / 残 S8-b)
- [ ] Phase 5 一致クラスの拡張 📋

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
| **符号→ambient の共有層 (S1)** | `ChannelCoding/CodeToAmbient.lean` (469 行 / 12 decl、MAC/BC 共有) | `isMarkovChain_of_compProd_pi:203` (conditioner 一般形) / `isMemorylessChannel_of_compProd_pi:315` / `le_log_of_ceil_exp_le:461` |
| **BC の符号→ambient 橋 (S2–S6)** | `BroadcastChannel/OuterBoundUV/Bridge.lean` (952 行 / 59 decl) | `bcConverseAmbient:141` → 構造前提 4 本 `:301`–`:428` → `bcConverseFanoSlack₁/₂:532`/`:541` → `bc_uv_converse_from_code:562` / `bc_uv_rate_extract:602` → `uvAuxPad:663` + 不変性 `:729`–`:754` |
| **UV per-letter 情報スロット (S6)** | 同ファイル `:780`–`:948` (`section PerLetterInfo`) | `uvInfo₁:793` / `uvInfo₂:798` / `uvInfoSum₂:803` / `uvInfoSum₁:808` (5 つ組法 `ν` の 1 引数汎関数) + `bcUVTuple:825` / `bcUVJointDistribution:849` + 同定 4 本 `:865` / `:883` / `:900` / `:925` |
| **UV 外界の集合版 (S7)** | `BroadcastChannel/OuterBoundUV/Assembly.lean` (1179 行 / 65 decl) | チャネル整合条件 `IsUVChannelLaw:119` + 特徴づけ `isUVChannelLaw_iff:155` + 閉包性 `.smul:177` / `.add:184` / `.finsetSum:192` / `.map_auxiliaries:207` / `.map_input_output:234`。領域 `uvRegion:265` / `bcOuterRegionUV:277` / `bcOuterRegionUV_isClosed:283` / `bcOuterRegionUV_nonempty:333`。符号側の支払い `bcUVJointDistribution_isUVChannelLaw:384`。非退化の証拠 `not_isUVChannelLaw_uvOutputCopiesInputLaw:474` / `not_isUVChannelLaw_uvAuxCopiesOutputLaw:549` |
| **時間共有 + 平均化 (S8-a)** | 同ファイル `section Averaging:593`–`:731` / `section AuxRelabel:735`–`:823` / `section TimeSharing:827`–`:1177` | 混合法 `bcUVTimeShare:866` (+ `_isUVChannelLaw:892` / `_eq_sum:880`) と 4 スロットの平均化 `bcUVTimeShare_uvInfo₁_ge:923` / `_uvInfo₂_ge:941` / `_uvInfoSum₂_ge:1018` / `_uvInfoSum₁_ge:1026`。補助アルファベットの `ℕ` 付け替え `uvRelabel:742` + スロット不変 4 本 `:751` / `:763` / `:783` / `:803`。到達点 `bc_uv_shrunk_point_mem:1052` |
| 汎用資産 (S7/S8-a 自作、BC 非依存) | 同ファイル `compProd_comap_map_prodMap:125` / `compProd_pi_map_pair_eq_of_update_invariant:347` / `condMutualInfo_compProd_fst_eq_lintegral:640` / `condMutualInfo_compProd_snd_eq_lintegral:702` / `le_toReal_of_inv_mul_le:1036` | Mathlib 不在で自作。`compProd_pi_map_pair_eq_of_update_invariant` は `CodeToAmbient.lean:344` の `compProd_pi_map_pair_eq` の strict generalization (監査が機械確認)。`condMutualInfo_compProd_*_eq_lintegral` は**絶対連続性の仮説を持たない等式** |
| `csiszar_sum_identity_cond` | `OuterBoundUV/Gateway.lean:246` | 条件付き Csiszár 和恒等式 (異アルファベット + 背景 conditioner)。Phase 4a の核 |
| `csiszar_sum_identity` | `BroadcastChannel/ConverseGateway.lean:142` | 無条件版 (同一アルファベット) |
| `bc_converse` / `bc_input_singleletterize` | `BroadcastChannel/Converse.lean:571` / `:316` | degraded 限定の converse。Phase 5 の接続先。**これも floating 形** |
| `bc_achievability` | `BroadcastChannel/Achievability/Assembly.lean:1093` | degraded 限定の達成側。Phase 5 の接続先 |
| `marton_achievability` | `Marton/Achievability.lean:767` | 一般 BC 内界 (EGK Thm 8.3、private message のみ) |
| `InMartonRegion` | `Marton/Basic.lean:40` | 3 不等式バンドル (点ごと述語) |
| `MACAchievable` / `macPentagon` / `macCapacityRegion` | `MultipleAccess/TimeSharing.lean:49` / `:58` / `:66` | 操作的述語 → closure で集合化のパターン |
| **MAC の符号→ambient 橋** | `MultipleAccess/TimeSharingConverse/Bridge.lean` (847 行 / 37 decl) | **S6 の雛形 (消化済)**。per-letter 同定は `macConverse_map_triple_eq:718` → 同定 3 本 `:771` / `:797` / `:823` |
| **MAC の集合化 + 極限** | `MultipleAccess/TimeSharingConverse/Assembly.lean` (953 行 / 12 decl) | **S8 の雛形**。`bc_capacity_subset_uv` の対応物は `mac_timesharing_converse:817` / `mac_timesharing_capacity_region:908`。退化レート被覆に `:397`–`:817` で約 450 行。兄弟 `mac_converse_shrunk_point_mem:129` は `0 ≤ R₁` を持つ弱い形 (BC 側は持たない = より強い) |
| `mac_avgPentagon_mem_convexHull` | `TimeSharingConverse/Bridge.lean:99` | n 文字平均を単一文字分布の凸包へ落とす先例。**4b では不採用** (判断ログ 5) |
| `mac_capacity_region_reconciliation` | `MultipleAccess/Reconciliation.lean:292` | 内外を同じ言語に揃える先例 |

**存在しないもの**: `bc_capacity_subset_uv` (= Phase 4b の到達目標)。
less noisy / more capable / semi-deterministic のクラス定義 (project 全体で 0 hit)。
per-letter の情報スロットは S6、UV 外界の集合版とチャネル整合条件は S7、
4 スロットの平均化 `(n)⁻¹ ∑ᵢ slotₖ(νᵢ) ≤ slotₖ(mixture)` は S8-a で実在化した。

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
  構成する橋と、n 文字の平均を単一文字補助変数の分布へ落とす還元。情報量の議論は一切増えない。

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

### Phase 4b — UV 外界の集合化 + 操作的包含 🚧 ★本命・最重量

到達目標は `bcOuterRegionUV W : Set (ℝ × ℝ)` と
**`bc_capacity_subset_uv : bcCapacityRegion W ⊆ bcOuterRegionUV W`**。
step 分解の SoT は在庫 §「step の推奨分割」。依存順は `S1 → S2 → S3 → S4 → S6 → S7 → S8`、
`S5` は `S1` 直後に並行着手可。

**完了分** — 在庫が挙げた難所 3 つのうち **難所 1 (構造前提の構成側導出) と難所 2 (補助変数の
型統一) は closure**、S7 が積み残した情報量の平均化も S8-a で closure。残るのは
難所 3 (退化レート被覆) + 極限 = S8-b の 1 step。

| step | 成果 | commit |
|---|---|---|
| M0 在庫 | [`bc-uv-operational-inventory.md`](bc-uv-operational-inventory.md) — MAC 橋の全 decl を `reuse` / `mirror` / `restructure` / `absent` に分類。全体 ≈ 1370 行、**Mathlib 側に自作が要る穴はゼロ** = `@residual(wall:…)` 候補なし | — |
| S1 共有化 | `ChannelCoding/CodeToAmbient.lean` 新設 (MAC/BC 共有)。MAC `Bridge.lean` の汎用補題 11 本を移設して public 化 (MAC 側は 1238 → 847 行) | `278977c2` `1c6c69aa` |
| S2 BC ambient 構成 | `OuterBoundUV/Bridge.lean` 新設。ambient 測度の構成一式 (25 decl)。出力空間を `Fin n → β₁ × β₂` に固定した結果 `bcConverseKernel c W m = c.blockOutputLaw W m` が `rfl` で成立 | `a6fd1ec5` |
| S3 構造前提の導出 | **難所 1**。`bc_uv_converse` が要求する構造前提 4 本 (`h_memo₁/₂` `hmarkov₁/₂`) を ambient の構成から導出。**`OuterBoundUV.lean` は無改変** (判断ログ 3・6) | `6275f2bb` `2e5b248f` |
| S4 符号レベル converse | `bcConverse_errorProb₁/₂_eq` + `bc_uv_converse_from_code` (`@[entry_point]`) + `bc_uv_rate_extract` | `51d5bcf9` |
| S5 補助変数の型統一 | **難所 2**。`uvAuxPad` による補助変数の型統一 + 相互情報量 / 条件付き相互情報量の不変性 (L-BCO5 不発動) | `5fd4d3ce` `4fd80cd3` |
| S6 per-letter 同定 | `uvInfo₁/₂/Sum₁/Sum₂` (5 つ組法 `ν` の 1 引数汎関数) + `bcUVTuple` / `bcUVJointDistribution` + 同定 4 本。攻略路は S5 の pad 不変性 → `mutualInfo_map_comp` / `condMutualInfo_map_comp` で、**自作補助補題ゼロ**。副次的に Fano slack を `bcConverseFanoSlack₁/₂` に略記化 | `c67f756c` `45807dcc` |
| S7 集合化 | `OuterBoundUV/Assembly.lean` 新設 (root 登録済)。判断ログ 9 の 2 条件を `IsUVChannelLaw` = **1 本の合成積恒等式**で同時に課し、`isUVChannelLaw_iff` で**反例 class ごと閉じた**。補助変数の型量化は両方 `ℕ` に固定して回避。実測 400 行 (在庫見積り 250 行 + 汎用輸送補題 2 本) | `e9682e21` `d0418dbd` `ae72035d` |
| S8-a 情報量の平均化 | 同ファイルに +591 行 (588 → 1179)。時間共有済み混合法 `bcUVTimeShare` を符号から構成し、4 スロットすべてで `(n)⁻¹ ∑ᵢ slotₖ(νᵢ) ≤ slotₖ(mixture)` を確立。**到達点 `bc_uv_shrunk_point_mem` は無条件宣言** (仮説は regularity のみ)。副産物として BC 非依存の汎用補題 `condMutualInfo_compProd_fst/snd_eq_lintegral` / `le_toReal_of_inv_mul_le` / `uvRelabel` + スロット不変 4 本。honesty ゲート ALL OK (`@audit:ok`) / style ゲート PASS | `31b8d2a3` `a069be70` `c65b7094` |

**残 step**

- [ ] **S8-b 退化レート被覆 + 極限** (**難所 3**) — Fano slack → 0 の極限 + `bc_capacity_subset_uv`。
      `bc_uv_shrunk_point_mem` は `2 ≤ M₁` / `2 ≤ M₂` / `0 < n` を要求するが、`R₁ ≤ 0` では
      `BCAchievable` が `M₁ = 1` の符号しか保証しない (MAC は同じ箇所に約 450 行)。
      **退避は L-BCO6** = 第一象限交差版で先に閉じる
- [ ] `bcOuterRegionUV ⊆ bcOuterRegionCoop` を示せれば「UV は協調外界より狭い」が機械可読になる
      (**任意**。示せなくても挟み込みは 2 本並立で成立する)

**S8-b の分類は `wall:` ではなく `plan:` が正しい** (S7 の honesty 監査が確認): Mathlib には
`mutualInfo` の定義自体が無い (`rg "def mutualInfo" .lake/packages/mathlib/` = 0 file) ので MI 層は
全部 in-project 資産 ⟹ この層で Mathlib gap は原理的に成立しない。

**ファイル配置**: S6 は `OuterBoundUV/Bridge.lean` に着地済 (952 行で 1500 行ガイド内)。
S8-b も S7/S8-a と同じ `.../OuterBoundUV/Assembly.lean` に載る (分割の判断 → 後続 leg の任意作業 6)。

**S8-b への申し送り (S8-a の実装者と honesty 監査が凍結した形、すべて実測)**

- **入口の確定形**: `bc_uv_shrunk_point_mem` (`Assembly.lean:1052`) が
  `(R₁ - (F₁+F₂)/n, R₂ - (F₁+F₂)/n) ∈ bcOuterRegionUV W` を**無条件に**返す
  (`F₁ = bcConverseFanoSlack₁ c W`)。仮説は `0 < n` / `2 ≤ M₁` / `2 ≤ M₂` /
  `⌈exp (n R)⌉ ≤ M` + 有限アルファベット (`Fintype α/β₁/β₂` は section variable) のみ。
  S8-b は**この点列の極限を取るだけ**で、情報量の議論は増えない
- **領域定義の確定形 (SoT)**:
  ```
  bcOuterRegionUV W = closure (⋃ (ν : ProbabilityMeasure (ℕ × ℕ × α × β₁ × β₂))
                                 (_ : IsUVChannelLaw W ↑ν), uvRegion ↑ν)
  uvRegion ν = {p | InBCOuterRegionUV p.1 p.2 (uvInfo₁ ν).toReal (uvInfo₂ ν).toReal
                      (uvInfoSum₂ ν).toReal (uvInfoSum₁ ν).toReal}
  ```
  closure は不可避 (半平面の交差の union は閉じない) だが、それが `bcOuterRegionUV_isClosed` を
  無料にし `bcCapacityRegion = closure {achievable}` との接続 (`IsClosed.closure_subset_iff`) に効く。
  **第一象限制約なし** (判断ログ 1) — 兄弟 `mac_converse_shrunk_point_mem` が持つ `0 ≤ R₁` を
  持たない**より強い形**
- **極限の作り方**: Fano slack → 0 は `bcConverseFanoSlack₁/₂` (`Bridge.lean:532`/`:541`) に
  `bcConverse_errorProb₁/₂_eq` を `rw` して `averageErrorProb` の極限に落とすのが素直。
  `le_toReal_of_inv_mul_le` (`Assembly.lean:1036`) は極限側でも効く見込み
- **順序制約 (実測)**: 補助変数を `ℕ` へ付け替えるのは平均化の**後**。`ℕ` 上で先に平均化すると
  有限性 (`mutualInfo_ne_top`) が取れず詰む。`uvRelabel` の注入は
  `exists_injective_nat` + `Function.invFun` + `measurable_of_countable` の 3 点セットで作る
- **`condMutualInfo_map_comp` は `rw` が通らない** (`[IsFiniteMeasure]` インスタンス引数依存で
  「motive is not type correct」)。`ρ = μ.map T` を仮説で受ける版
  **`condMutualInfo_map_comp'` (`ChannelCoding/CodeToAmbient.lean:442`)** を使う
- **`Fintype.card (Fin M) ≢ M` の摩擦は S7 でも S8-a でも出なかった** (実測)。
  `bc_uv_shrunk_point_mem` は `2 ≤ M₁` を素の `ℕ` 不等式で取るので、S8-b でも
  `bc_uv_converse` を直接適用しない限り出ない見込み
- `uvInfoSum₁/₂` の**下付き数字は受信機番号ではなく「先頭に来る corner 項の選択」** (両方とも
  `R₁ + R₂` の上界)。宣言順 `uvInfo₁, uvInfo₂, uvInfoSum₂, uvInfoSum₁` は `InBCOuterRegionUV` の
  フィールド順 (`bound₁, bound₂, sumBound₂, sumBound₁`) に合わせた意図的なもの

**実装時に効く唯一の制約**: `bcConverseAmbient` の出力空間を **`Fin n → β₁ × β₂` (対の列)** に
固定する (S2 で確定済)。`(Fin n → β₁) × (Fin n → β₂)` (列の対) に取ると `Measure.pi` の構造が
壊れ、S3 の結合 Markov が構成側から出なくなる (判断ログ 3)。

proof-log: **yes** (`docs/proof-logs/proof-log-bc-uv-operational.md`)。橋の構成は再利用先が
degraded 側にもあり、MAC からの読み替えで何が効かなかったかを残す価値がある。

### Phase 5 — 一致するクラスを広げる 📋

degraded は既に閉じている。その一般化を、Phase 1 の内界と Phase 4 の外界の組で回収する。

- [ ] クラス定義の新設 (project に 0 hit): more capable / less noisy / semi-deterministic
      — **4b と独立に着手できる**。等号を述べる前でも定義と基本性質は入る
- [ ] **semi-deterministic BC** (Marton 1979) — Marton 内界 = 容量領域が既知。**Phase 4b が事実上の
      前提**: 等号を述べるには内界と外界を同じ言語 (集合) で比較する必要があり、4a の floating 形
      では `martonRegion` と並べられない
- [ ] more capable / less noisy — 外界が UV より単純な形を取る (El Gamal 1979)
- [ ] degraded を新クラスの特殊化として既存 `bc_converse` / `bc_achievability` に接続。
      `bc_converse` 自身も floating 形なので、ここでも 4b の橋が効く
- [ ] **着手前に 1 度確認すること (S8-a の honesty 監査からの引き継ぎ)**: `uvRegion` のスロットが
      `.toReal` を通るため `⊤` が `0` に潰れる。この非対称性は**外界 (converse) 方向では領域を
      狭める = 主張を強める側なので安全**だが、**逆包含 (achievability / 領域 ⊆ operational) を
      証明する段では逆向きに効く**。等号を述べるのは Phase 5 なので、向きの確認はここが期限

proof-log: 未定 (クラス定義段は no、等号が閉じたら yes)。

## 後続 leg の任意作業 (Phase 4b の完遂条件ではない)

style / honesty ゲートが提起し、当該 leg では見送った項目。S8 の前提ではない。

1. `uvAux_pad_mutualInfo_prod_eq` の `prod` が何の直積か名前から読めない (実際は左引数で補助変数と
   `Xs` を対にする)。`uvAux_pad_pair_mutualInfo_eq` 等へのリネーム提案。consumer は in-file 1 件
   (`uvAux_pad_condMutualInfo_eq`、`scripts/dep_consumers.sh` 実測)
2. `mutualInfo_eq_of_leftInverse` (`OuterBoundUV/Bridge.lean`) は BC 固有要素ゼロの汎用補題で、
   `DPI.lean` へ移すのが `docs/rules/module-structure.md` 準拠。移設だけなら consumer は in-file
   2 件。ただしこれは `MIChainRule.lean` の `mutualInfo_map_left_measurableEquiv` (より強い
   `MeasurableEquiv` 仮説) を subsume するので、**置換まで行くなら直接 touch 対象は 17 decl /
   11 file** (`scripts/dep_consumers.sh` 実測、MAC 系・BC 系・WZ 系にまたがる)。移設と置換は
   別 leg に割るのが安全
3. `CodeToAmbient.lean` の移設由来 6 本 (`compProd_pi_map_pair_eq` / `mutualInfo_map_comp` /
   `condDistrib_map_comp` / `condMutualInfo_map_comp` / `condMutualInfo_map_comp'` /
   `le_log_of_ceil_exp_le`) が無タグ。file 全体のタグ被覆を揃えるなら別 leg
4. `CodeToAmbient.lean` に `show` → `change` の linter 警告が 1 件 (S1 の移設由来、`lake build`
   でのみ出る)
5. **section 再配置による逐語コピーの完全畳み込み (残 ~30 行)**。S6 は Fano slack の略記化ぶんしか
   取れず (見積り「~70 行消える」に対し実測 net −26 行 = statement が定理あたり 22 行 × 2 縮み、
   def が 18 行増)。`∑ i, uvInfo₁ (bcUVJointDistribution c W i)` 形への完全な畳み込みは現配置では
   不可能 — `bcUVJointDistribution` は `uvAuxPad` に依存し、`uvAuxPad` は `bc_uv_converse_from_code`
   より**後ろ**にある。取りに行くなら `section Pad` + `section PerLetterInfo` を `section CodeLevel`
   の**上**へ移す再配置が要る。S8 で序でにやってもよいが、完遂条件ではない
6. **`Assembly.lean` の分割 + BC 非依存の汎用補題の移設**。現在 1179 行で、S8-b が MAC 並み
   (+450 行) に膨らむと ≈1630 行で 1500 行ガイドを超える。降ろせる BC 非依存分が既に ≈200 行:
   `section Averaging` (`:593`–`:731`) + `compProd_comap_map_prodMap` (`:125`) +
   `compProd_pi_map_pair_eq_of_update_invariant` (`:347`)。移設先候補は
   `Shannon/CondMutualInfo.lean` 近傍 / `ChannelCoding/CodeToAmbient.lean`。
   **import DAG の注意**: `condMutualInfo_eq_of_leftInverse_cond` が
   `mutualInfo_eq_of_leftInverse` (`OuterBoundUV/Bridge.lean:713`) を消費するので、そちらも
   一緒に降ろすか新ファイルが `Bridge.lean` を import するかの選択が要る。
   **判断: 分割は S8-b の後** — S8-b の実測行数が出てから 1 回で切る方が、予測で切るより
   切り直しが要らない。着手前に `scripts/dep_consumers.sh --transitive` を引くこと。
   なお `compProd_pi_map_pair_eq_of_update_invariant` は `CodeToAmbient.lean:344` の
   `compProd_pi_map_pair_eq` の strict generalization であり、**移設でなく置換まで行くと MAC 系の
   再ビルドを伴う**: 被置換側の consumer は direct 1 decl / 1 file
   (`TimeSharingConverse/Bridge.lean:712` = `macConverse_map_triple_eq`)、**transitive 12 decl /
   2 file** (MAC `Bridge.lean` 4 本 + `Assembly.lean` 8 本 = `mac_timesharing_capacity_region` まで
   到達、`scripts/dep_consumers.sh --transitive` 実測)。移設と置換は別 leg に割る
7. **規約どうしが同じケースで逆方向に引く件 (S8-a で実測データが揃った)**:
   `docs/rules/docstrings.md` item 1 (`## Main statements` 掲載定理には docstring 必須) と
   `scripts/lean_doc_lint.ts` の `internal-doc` ratchet (内部補題の散文 docstring 増加を NG とする)
   が構造的に衝突する。リンターは module doc の Main statements リストを見ないので、
   `@[entry_point]` もタグも無い theorem に散文 docstring を足すと 1 本あたり `internal-doc` +1。
   S8-a で `bc_uv_shrunk_point_mem` が通ったのは `@audit:ok` タグがあったから
   (`lean_doc_lint.ts:469`–`:478` が `@residual|@audit:` を含む docstring を skip する) で、
   一般には通らない。**現に `Assembly.lean` の Main statements 掲載でタグ無しが 6 本裸**:
   `isUVChannelLaw_iff` / `not_isUVChannelLaw_uvOutputCopiesInputLaw` /
   `not_isUVChannelLaw_uvAuxCopiesOutputLaw` / `condMutualInfo_compProd_fst_eq_lintegral` /
   `condMutualInfo_compProd_snd_eq_lintegral` / `bcUVTimeShare_uvInfo₁_ge` 系。
   解は「真の headline に `@[entry_point]` を付ける (リンターが除外)」か
   「module doc に散文を持たせる現行慣行を追認する」の二択で、**ファイル単体を超える方針判断**。
   参考: `OuterBoundUV/` 配下の `@[entry_point]` は `Bridge.lean:561` の 1 本のみ。
   **本 plan の範囲外** (`docs/rules/` 側の課題として起票)
8. **命名の軽微な逸脱** `condMutualInfo_eq_of_leftInverse_cond` (`Assembly.lean:604`) —
   `docs/rules/naming.md` §2 は `_of_` 以降を仮定列に充てるので、区別子 `_cond` は `_of_` の
   **前**に置くのが Mathlib 順。consumer は同ファイル内 2 箇所。優先度低

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

Phase 4b の 2 件 (単一文字還元の形 / 結合 memoryless の持ち方) は M0 在庫で決着 → 判断ログ 3・5。
後者は S3 で機械確認まで済んだ。

## 撤退ライン (frozen slug)

| slug | 発動条件 | 退避先 |
|---|---|---|
| **L-BCO1** | Phase 4 の補助変数 identification が閉じない | **不発動** — Phase 4a で `uvAux` 1 本の 2 通り instantiation により閉じたため、Körner–Marton / Sato への後退は不要になった |
| **L-BCO2** | Phase 2 の型量化 union が universe 問題で詰む | 濃度固定版で止め、union は取らない (Phase 3–5 は影響を受けない) |
| **L-BCO3** | Phase 5 の等号が Phase 4 の外界の形と噛み合わない | クラス定義だけ入れて等号は defer |
| **L-BCO4** | Phase 4b の符号→ambient 橋または単一文字還元が閉じない | **発動条件は S8-b だけに縮んだ** (橋は S1–S4、集合化は S7、平均化と `bc_uv_shrunk_point_mem` は S8-a で closure)。退避先の前半「`bcOuterRegionUV` の集合定義までは入れる」は S7 が、点の membership は S8-a が既に満たしており、残る退避は `bc_capacity_subset_uv` を `sorry` + `@residual(plan:bc-general-region-plan)` で残す形。残りを別 plan に切り出す場合は新 plan の filename を slug に合わせて `@residual(plan:<新 stem>)` に張り替える。**4a の floating 形 headline と S1–S8-a の成果は無傷で残るので、退避しても到達済の成果は減らない** |
| **L-BCO5** | S5 の補助変数の型統一が `mutualInfo_chain_rule` 経由でも閉じない | **不発動** — 在庫の攻略路 (両向き DPI + `mutualInfo_chain_rule` + `ENNReal.add_right_inj`) がそのまま効いた。退避先だった「`n` を露出した族 `bcOuterRegionUVAt W n` + `⋂ n` 版」は採らない (slug は他文書参照のため凍結) |
| **L-BCO6** | S8-b の退化レート被覆が MAC 同様 450 行級に膨らむ | `bc_capacity_subset_uv` を第一象限交差版 `bcCapacityRegion W ∩ {p \| 0 ≤ p.1 ∧ 0 ≤ p.2} ⊆ bcOuterRegionUV W` で先に閉じ、全平面版は後続 leg へ送る (MAC `mac_timesharing_capacity_region` と同じ形)。未達部分の退避出口は `sorry` + `@residual(plan:bc-general-region-plan)` |

**禁止事項**: どの撤退でも「外界が成立する」「補助変数が取れる」「符号から ambient が取れる」等を
`*Hypothesis` 述語に束ねて仮説として渡す形は取らない (CLAUDE.md 検証の誠実性 tier 5)。退避は
`sorry` + `@residual` で、署名は証明したい形のまま保つ。特に Phase 4b では、結合 memoryless を
「操作的構成から導けなかったので仮説で受け取る」と書き換えるのは、**それ自体は構造前提として
honest でありうる**が、`bcCapacityRegion ⊆ …` の左辺が符号を量化している以上、包含の主張から
仮説へ核が移動する形になっていないかを毎回確認する。

## 推奨実行順

**4b (S8-b 退化レート被覆 + 極限) → 5**。Phase 2 は独立で、いつ入れてもよいし入れなくても
本線は完結する。
Phase 5 のクラス定義だけは 4b と並行して着手できる。

## 判断ログ

1. **外界に第一象限制約を入れない**: `bcCapacityRegion` は**非正レート対を真に含む** (単一メッセージ
   符号で達成可能、Phase 1 の独立監査が特定)。外界に `0 ≤ R` を入れると包含が偽になる。Phase 3 は
   符号制約も入れない形を採り、レート上界が任意の実数レートで成立するため左辺との交差も不要だった。
   **`bcOuterRegionUV` の定義 (S7) でも同じ制約が効く** (容量は非負なので非正部分は損失にならない)。
2. **Phase 4 を 4a (情報量レベル) / 4b (操作的レベル) に分割**: 難所が「Csiszár の適用形」と
   「符号→ambient の橋 + 単一文字還元」で別物であり、前者だけでも独立した到達点になる。
   degraded 版 `bc_converse` も floating 形なので、4b の橋は 2 箇所に効く共有資産。
3. **結合 memoryless は構成側で持つ (既定 (b))** — **S3 で機械確認済**。座標ごとの条件付き独立は
   結合の条件付き独立を導かない (Phase 4a 独立監査) が、仮説を結合形に強める案 (a) は不要で、
   `h_memo₁/₂` `hmarkov₁/₂` は ambient の構成から出る。S3 の実装者と独立の honesty 監査者が
   それぞれ scratch で `bc_uv_converse` に 4 本を実引数として流し込み 0 errors で elaborate
   することを確認し、**`OuterBoundUV.lean` の署名は無改変で通った** (想定していた 6 decl の署名
   変更は発動せず)。成立は出力空間を `Fin n → β₁ × β₂` に取ることに依存する。
4. **Phase 5 の等号は Phase 4b が事実上の前提**: semi-deterministic BC の等号は内界と外界を同じ言語
   で比較する必要があり、4a の floating 形では `martonRegion` と並べられない。ただしクラス定義の
   新設 (less noisy / more capable / semi-deterministic) は 4b と独立に進む。
5. **単一文字還元は案 A (時間共有変数を補助変数に吸収) を採る (M0 在庫 表 3)**: MAC 式の凸包ルート
   (案 B) は `mac_avgPentagon_mem_convexHull` が必須で要求する `a i ≤ c i` の UV 対応が
   `I(Uᵢ;Y₁ᵢ) ≤ I(Uᵢ;Y₂ᵢ)` = less noisy 相当になり、**Phase 4a が獲得した「degradedness 前提なし」を
   失う** (在庫が反例で必須性を確認済)。加えて凸包はつねに第一象限に閉じるので判断ログ 1 と衝突し、
   到達目標が交差版に弱まる。案 A の対価だった型統一層は S5 で支払い済なので、S7 は凸幾何を
   持ち込まずに書ける。
6. **一般化の方向が在庫の予想より 1 段広かった (S3)**: `isMemorylessChannel_of_compProd_pi` の
   一般化は在庫が想定した「conditioner にメッセージ成分を足す」ではなく、**「conditioner を任意の
   update 不変写像に開く」** 形 (`isMarkovChain_of_compProd_pi`) になった。結果、在庫が別工程と
   見ていた「対の列を 2 本の列に分ける整形層」が conditioner に吸収されて丸ごと消えた。以後の
   一般化も「仮説を足す」より先に「補題が実際に使っている性質まで緩める」を試す。
7. **在庫 表 1-B の `macConverseInput_eq` = `absent` は誤り (S4 が是正)**: 在庫は「合同復号器用
   なので受信機別復号の BC には不要」としたが、`averageErrorProb₁/₂` が `M₁ * M₂` で正規化して
   メッセージ**対**について和を取るため、対一様性の同定は受信機別の誤り確率同定**両方**に要る。
   S4 が `bcConverseInput_eq` (`OuterBoundUV/Bridge.lean:186`) として自作 (15 行)。在庫ファイル
   自体は編集しないので、本エントリが訂正の SoT。
9. **union の添字を縛る 2 条件は `IsUVChannelLaw` 1 本 = 単一の合成積恒等式で解決した (S7)**:
   `uvInfo*` は 5 つ組法 `ν` の 1 引数汎関数でチャネル `W` を引数に取らないため、
   `bcOuterRegionUV W` を「任意の `ν` にわたる union」として定義すると、出力を入力にコピーする
   `ν` が全仮説を満たしつつ 4 スロットを任意に大きくでき、**外界が平面全体に退化して
   `bc_capacity_subset_uv` が vacuous に真になる** (S6 の honesty 監査が特定した反例 class、
   単一 instance ではなくアルファベット拡大で無限に構成できる)。⟹ union の添字には
   (i) 出力の条件法が `W` に一致、(ii) 補助 → 入力 → 出力の Markov 性、の 2 条件が要る。
   S7 はこれを別々の述語にせず、5 つ組法 `ν` を
   `((U,V,X),(Y₁,Y₂))` へ押し出したものが `(U,V,X)` 周辺と `W` の合成積に一致する、という 1 本の
   等式で同時に課す。honesty 監査が**反例 class ごと閉じたことを機械確認**: `isUVChannelLaw_iff` が
   「`IsUVChannelLaw W ν` ⟺ `ν` = 補助と入力の同時法をチャネルに通したもの」を与える (5 つ組の
   再結合写像が可測全単射なので恒等式が `ν` 自身を pin する) ⟹ union の添字は「補助と入力の任意の
   同時法をチャネルに通したもの」**ちょうど**であり、コピー型の反例 class 全体が一括排除される。
   非退化の証拠は code 側に named theorem として残した:
   `not_isUVChannelLaw_uvOutputCopiesInputLaw` (条件 (i) 破り) と
   `not_isUVChannelLaw_uvAuxCopiesOutputLaw` (**(i) は満たすが (ii) 破り**、容量 0 のチャネル上で
   `I(U;Y₂) = log 2 > 0` を持つ = 通れば実際に外界を膨らませる無害でない候補)。
   監査の判定は「`IsUVChannelLaw` は load-bearing hyp ではなく**包含の右辺を縮める構造条件**」
   — 仮定しても証明すべき核は消えず、むしろ符号側で構成的に示す義務が増える
   (`bcUVJointDistribution_isUVChannelLaw` として支払い済)。
   あわせて**補助変数の型量化は両方 `ℕ` に固定して回避**した: 反例 class の議論が要求した
   「共通の有限型へ inject」は `ℕ` への relabel で足り、輸送は `IsUVChannelLaw.map_auxiliaries`
   が担う。
10. **在庫が「危険」と名指しした箇所が、場合分けで丸ごと消えた (S8-a)**: 本 plan は S8-a の危険箇所を
    `klDiv_compProd_lintegral` 経由の `h_ac` (対の法 ≪ 周辺の積、fiberwise) と名指ししていたが、
    実測では `by_cases h_ac` の否定側が `klDiv_of_not_ac` (KL = ∞) +
    `lintegral_eq_top_of_measure_eq_top_ne_zero` + `Measure.absolutelyContinuous_compProd_right_iff`
    で **∞ = ∞** に落ち、新設した `condMutualInfo_compProd_fst_eq_lintegral` は
    **絶対連続性の仮説を一切持たない等式**になった (離散性論法も不要)。同様に「S8 の必読事項」と
    していた先例 `mutualInfoPmf_mixture_affine` は**使われなかった** — 機構の指摘 (分岐エントロピーの
    相殺) 自体は正しいが、測度レベルでは「連鎖律 + タグ項の相殺」として実現され pmf レベルの有限和
    代数を経由しない (加えて橋 `mutualInfoPmf_empirical_eq_mutualInfo` は `WynerZiv/Operational.lean`
    で `private`)。一方 ⚠️ 警告として挙げた `klDiv_mixture_le` (`RateDistortion/Convexity.lean:336`、
    向きが逆) は一度も掴まれておらず、**警告は有効に機能した**。
    **在庫予測の外れとしてはこれで 5 件目** (先行 4 件 = 判断ログ 6 / 7 / 9 + 0-hit 見落とし)。
    外れ方の型が今回は新しい: これまでは「在庫が挙げていない難所が出た」型だったが、今回は
    **「在庫が名指しした危険が場合分けで消えた」型** = over-estimation 側。⟹ 以後、在庫の危険箇所は
    「回避不能な難所」ではなく「**分岐で消えるか 1 度試すべき候補**」として扱う。
    一般に、危険と名指しされた仮説は退化枝を `by_cases` で切ると両辺が同じ極値に落ちて要らなくなる
    ことがある。在庫ファイル自体は編集しないので、本エントリが記録の SoT。
