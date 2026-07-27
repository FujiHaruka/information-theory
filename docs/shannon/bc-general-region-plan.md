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
        S0–S2 ✅ `06817339` `32385115` `a97fde13` / **S3–S8 📋 ★次の一手**

## 在庫

| 資産 | 場所 | 用途 |
|---|---|---|
| `BCAchievable` / `bcCapacityRegion` | `BroadcastChannel/Operational.lean:53` / `:68` | 主語。包含の左辺 |
| `bc_capacityRegion_isClosed` / `bc_achievable_mono` / `bc_mem_closure_of_strictly_below` | `Operational.lean:102` / `:71` / `:86` | 閉性・down-set 性・厳密不等号からの closure 回収 (3 本目が内界包含の主役) |
| `martonRegion` / `bc_strict_interior_achievable` / `marton_region_subset_capacity` | `Operational.lean` (168 行 / 8 decl) | Marton 内界の集合版と包含 (`@[entry_point]`)。**符号制約なしの全平面版** (`2c938fe0`) |
| **比較クラス 3 本 + 包含鎖** | `BroadcastChannel/Classes.lean` (253 行 / 9 decl) | `IsBCLessNoisy:63` / `IsBCMoreCapable:75` / `IsBCSemiDeterministic:83` と `@[entry_point]` 4 本 `bc_lessNoisy_infoJoint_ge:95` / `IsBCDegraded.isBCLessNoisy:133` / `IsBCLessNoisy.isBCMoreCapable:218` / `IsBCSemiDeterministic.exists_prob_real_singleton_eq_zero:236`。語彙橋 2 本 `bcJointDistribution_id_eq:166` / `mutualInfoOfChannel_map_eq_mutualInfo_bcJointDistribution:184`。**`IsBCLessNoisy` は `∀ (U : Type u) [Fintype U]` を量化する** — `ℕ` にも `ULift.{u} ℕ` にも当たらない (在庫 §Q2-3 に逐語エラー) ので、**量子化 → less noisy の順**に固定 |
| `bcOuterRegionCoop` / `bc_capacity_subset_coop` | `OuterBound.lean:380` / `:408` | 協調外界と包含 (`@[entry_point]`)。挟み込みの右辺その 1 |
| `BroadcastCode.restrict₁/₂` / `coop` + 誤り確率補題 | `OuterBound.lean:50`–`:262` | BC 符号 → 単一ユーザー符号への 3 通りの還元 |
| `channelCoding_operational_rate_le_capacity` | `ChannelCoding/StrongConverseAsymptotic.lean:805` | 操作的レート ≤ 容量 (`@[entry_point]`)。Phase 3 の心臓 |
| `uvAux` / 単一文字化 4 本 / `InBCOuterRegionUV` / `bc_uv_converse` | `OuterBoundUV.lean:71` / `:113` `:174` `:684` `:637` / `:735` / `:815` | Phase 4a。`uvAux` の**型が letter `i` に依存する**のが S5 の型統一の理由。headline は degradedness 前提なし (`@[entry_point]`) |
| **符号→ambient の共有層** | `ChannelCoding/CodeToAmbient.lean` (539 行 / 15 decl、MAC/BC 共有) | `isMarkovChain_of_compProd_pi:210` / `isMemorylessChannel_of_compProd_pi:322` / `le_log_of_ceil_exp_le:518` + BC 由来の汎用 3 本 (`compProd_comap_map_prodMap:346` / `compProd_pi_map_pair_eq_of_update_invariant:396` / `le_toReal_of_inv_mul_le:528`) |
| **BC の符号→ambient 橋 + UV per-letter 情報スロット** | `BroadcastChannel/OuterBoundUV/Bridge.lean` (936 行 / 58 decl) | `bcConverseAmbient:141` → 構造前提 4 本 `:301`–`:428` → `bcConverseFanoSlack₁/₂:532`/`:541` → `bc_uv_converse_from_code:562` / `bc_uv_rate_extract:602` → `uvAuxPad:663` + 不変性 `:713`–`:738`。`section PerLetterInfo` (`:764`–`:934`) が 4 スロット `uvInfo₁:777` / `uvInfo₂:782` / `uvInfoSum₂:787` / `uvInfoSum₁:792` + `bcUVTuple:809` / `bcUVJointDistribution:833` + 同定 4 本 |
| **UV 外界の集合版** | `OuterBoundUV/Region.lean` (474 行 / 33 decl) + `OuterBoundUV/Assembly.lean:72` | チャネル整合条件 `IsUVChannelLaw:104` + 特徴づけ `isUVChannelLaw_iff:125` + 閉包性 5 本 + `IsUVChannelLaw.map_input_output:228` / `.swap_auxiliaries:203`。領域 `uvRegion:259` / `bcOuterRegionUV:271` / `_isLowerSet:291` / `_isClosed` / `_nonempty`。非退化の証拠 2 本。符号側の支払い `bcUVJointDistribution_isUVChannelLaw` だけ `Assembly.lean:72` |
| **時間共有 + 平均化 + 極限 + headline** | `OuterBoundUV/Assembly.lean` (851 行 / 35 decl) | 混合法 `bcUVTimeShare:258` (+ `_isUVChannelLaw:284` / `_eq_sum:272`) と 4 スロット平均化 `bcUVTimeShare_uvInfo₁_ge:315` 系。縮小点の**乗法形** `bc_uv_code_point_mem:609` → `bc_uv_rate_point_mem:635` → `bc_uv_shifted_point_mem:696` → `bc_uv_quadrant_mem_of_achievable:784` → headline `bc_capacity_subset_uv:839` (`@[entry_point]`)。退化被覆は `bc_achievable_clamp_iff:670` + 下方集合性 |
| 汎用資産 (BC 非依存、自作) | `CodeToAmbient.lean` の 3 本 / `Shannon/CondMutualInfoMixture.lean` (193 行 / 7 decl) | 再符号化不変 3 本 `mutualInfo_eq_of_leftInverse:40` / `mutualInfo_congr_ae:57` / `condMutualInfo_eq_of_leftInverse_cond:66` + 混合法 4 本 `condMutualInfo_compProd_fst_eq_lintegral:102` / `mutualInfo_compProd_eq_add_lintegral:142` / `condMutualInfo_compProd_snd_eq_lintegral:164` (後 3 本が **S5 の裾評価 / S6 の核**)。混合法は**絶対連続性の仮説を持たない等式** |
| `csiszar_sum_identity_cond` / `csiszar_sum_identity` | `OuterBoundUV/Gateway.lean:246` / `BroadcastChannel/ConverseGateway.lean:142` | 条件付き Csiszár 和恒等式 (Phase 4a の核) と無条件版 |
| `bc_converse` / `bc_input_singleletterize` | `BroadcastChannel/Converse.lean:571` / `:316` | degraded 限定の converse (floating 形)。**degradedness を `h_deg_block` で受ける**ので 4b の橋はそのままでは効かない (判断ログ 11-(n)) |
| **達成側の共通形 3 本 + degraded headline** | `BroadcastChannel/Achievability/Assembly.lean` | `bc_ceil_exp_max_zero:1080` / `bc_Ec_lt_of_clamped_rate:1090` / **`bc_achievability_of_rate_lt:1103`** (レートの符号制約なし、`hJlt : max R₁ 0 + R₂ < bcInfoJoint`) / `bc_achievability_of_infoJoint_ge:1239` (`hsum` 形) / `bc_achievability:1270` (**署名・結論は逐語不変**) / `bc_degraded_infoJoint_ge:967` |
| **superposition 内界 (S0–S2)** | `BroadcastChannel/SuperpositionRegion.lean` (150 行 / 4 decl、import 3 本) | `bcInfo₁_nonneg:50` / `@[entry_point]` `bc_lessNoisy_achievability:84` / def `bcSuperpositionRegionFullSupport:119` / `@[entry_point]` `bcSuperpositionRegionFullSupport_subset_capacity:130` (仮説は `hW` + `hln` のみ)。**less noisy の言葉で挟み込みが並ぶ** |
| **内界の Marton union** | `BroadcastChannel/MartonUnion.lean` (110 行 / 5 decl) | `bcAuxAlphabet:52` (`= ULift.{u} (Fin (k+1))`) / `martonRegionUnion:58` / `martonRegionUnionFS:68` + `@[entry_point]` 2 本 `martonRegionUnion_subset_uv:81` (明示仮説ゼロ) / `martonRegionUnionFS_subset_capacity:101` + `_subset_union:88`。**superposition 路の補助アルファベットとしても再利用中** |
| `marton_achievability` / `InMartonRegion` | `Marton/Achievability.lean:767` / `Marton/Basic.lean:40` | 一般 BC 内界 (EGK Thm 8.3、private message のみ、**共通補助 `U₀` なし**) と 3 不等式バンドル |
| **内外の橋 (S1–S6、全段 proof done)** | `OuterBoundUV/MartonBridge.lean` (553 行 / 32 decl) + `Region.lean:203` | `martonJointDistribution_isUVChannelLaw:70` → `martonSwapLaw:117` → `martonUVLaw:160` + `martonUVLaw_isUVChannelLaw:177` + 4 スロット保存 `uvInfo₁_martonUVLaw:186` 系 / `.toReal` 同定 3 本 `:228` `:240` `:252` / 和レート 4 本 `:447` `:469` `:493` `:509` (核は Markov 鎖 2 本 `:303` `:329` + 条件付き DPI) / `marton_region_subset_uv:530` (`@[entry_point]`) |
| 情報量の道具 | `Shannon/CondMutualInfo.lean:214` / `:356` / `ChannelCoding/ConverseMemorylessChainRule.lean:113` / `OuterBoundUV/Gateway.lean:194` | 連鎖律 `mutualInfo_chain_rule` / DPI `mutualInfo_le_of_markov` / 条件付き DPI `condMutualInfo_le_of_markov_joint` / `condMutualInfo_le_add_condMutualInfo` |
| エントロピー / MI ↔ エントロピー形 | `MaxEntropy/Basic.lean:229` / `MultipleAccess/Reconciliation.lean:45` / `Shannon/Entropy.lean:200` / `:42` / **`Shannon/Pi.lean:36`** | `entropy_le_log_card` (S5 裾評価) / `mutualInfo_toReal_eq_entropy_form` / `condMutualInfo_eq_condEntropy_sub_condEntropy` / `entropy_pair_eq_entropy_add_condEntropy` / **`entropy_measurableEquiv_comp`** (平坦↔入れ子の再ラベル。在庫が「自作」としたが一般形が既存、判断ログ 16) |
| MAC の先例 | `MultipleAccess/TimeSharing.lean:49`–`:66` / `TimeSharingConverse/Bridge.lean` / `Assembly.lean` / `Reconciliation.lean:292` | 操作的述語 → closure で集合化 / 符号→ambient 橋の雛形 / 内外を同じ言語に揃える先例。**退化被覆と平均化は雛形にならない** (判断ログ 11-(f)、在庫 §Q3-E) |

**存在しないもの** (等号が要求し、まだ書かれていないもの): (a) 逆包含
`bcOuterRegionUV W ⊆ bcSuperpositionRegionFullSupport W` (**等号に残る唯一の包含**、S3–S8)。
内訳は情報量スロットの同定 3 本 / `IsUVChannelLaw` から Markov 鎖を出す補題 (`rg` 実測 0 件) /
`ℕ` 補助の有限量子化 + 裾評価 / 時分割の補助への吸収 / 全支持への摂動。
(b) more capable の 3 制約を受ける structure (`InBCCapacityRegion` は 2 field)、
(d) `IsBCDegraded W` から `bcConverseAmbient` 上の per-letter Markov 鎖 `h_deg_block` を出す補題、
(e) `(mutualInfo μ Xs Xs).toReal = entropy μ Xs` と決定的写像の条件付きエントロピー消失
(semi-deterministic 用)。**Mathlib 側の穴はゼロ** (在庫 §Mathlib の壁、4 leg 連続で 0 件)。
旧 (a) 「`bcOuterRegionUV ⊆ martonRegionUnionFS`」は**偽**と判定された (判断ログ 18、
[`bc-facts.md`](bc-facts.md))。

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
内界は 2 本ある — Marton union (`martonRegionUnion`、一般 BC 向け・共通補助 `U₀` なし) と
superposition (`bcSuperpositionRegionFullSupport`、cloud + satellite)。**前者は劣化 BSC 対ですら
容量領域より真に小さい**ので、等号を狙うクラスでは後者を使う。Marton union は「一般 BC で成立する
内界」としての価値は不変で、順包含 `martonRegionUnion ⊆ bcOuterRegionUV` はそのまま残る。

## Phase 詳細

### Phase 1 — 主語を作る (操作的容量領域) ✅

`fd39ad95` `deb930a7`。`BCAchievable` / `bcCapacityRegion := closure {…}` / `martonRegion` を定義し、
`marton_region_subset_capacity` で内界を集合の言葉に載せた。proof-log: no。

### Phase 2 — 補助変数についての union 🔄

`martonRegion` は `(pV, K)` を引数に取る。真の Marton 内界は補助変数の型と分布についての和集合。
M0 在庫は [`bc-phase2-union-inventory.md`](bc-phase2-union-inventory.md) (Mathlib の壁 0 件)。

#### 最小完遂 P1–P3 ✅ (`ce8e9d0b` 在庫 / `fcdafaf5` 実装 / `b1837901` style)

`BroadcastChannel/MartonUnion.lean` (新設)。採った定義:

```
martonRegionUnion W = closure (⋃ k₁ k₂ (pV : Measure (bcAuxAlphabet k₁ × bcAuxAlphabet k₂)) _ K _,
                                 martonRegion pV K W)     -- bcAuxAlphabet k = ULift.{u} (Fin (k+1))
```

設計の 3 点はいずれも**機械確認済**なので蒸し返さないこと: (a) `Fin (k+1)` であって `Fin k` でない
— `k = 0` で `Nonempty` が出ず `martonRegion` のインスタンス要求を満たせない。(b) `ULift.{u}` が要る
— `IsBCLessNoisy` (`Classes.lean:63`) が `∀ (U : Type u)` を量化するので素の `Fin (k+1) : Type 0` は
universe mismatch。(c) `closure` を外側に取る — 比較先が閉集合なので包含に損がない。
**ファイル配置は `Marton/` 配下ではなくトップ直下** — `Marton/` は `OuterBoundUV/` を 1 本も import
しておらず、移すとディレクトリ間依存が双方向になり `docs/rules/module-structure.md` §5 を破る。
`bcAuxAlphabet` は superposition 路 (S0–S2) でもそのまま再利用できた。

⚠ **正直な限界 (実際に発火した)**: この `martonRegionUnion` は**時分割変数も共通補助 `U₀` も持たない
Marton 内界**で、EGK Thm 8.3 の `⋃ p(q,u,v,x)` 版より真に小さい。**劣化 BSC 対でこの限界が
`martonRegionUnionFS ⊊ bcCapacityRegion` として現れる** (判断ログ 18)。

#### 拡張 P4–P7 📋 (行数見積りは在庫 §12 が SoT)

**いずれも等号の前提ではない** (経路変更で P7 の位置づけが変わった)。API の完全性と L-BCO2 の完答。

- [ ] **P4** 非空性 / 下方集合性 (~30 行、`Region.lean` の外界版が雛形)
- [ ] **P5** `Convex ℝ (martonRegion pV K W)` (~20 行、任意)。probe 実測済
- [ ] **P6** 補助アルファベットの付け替え不変性 (~110 行)。**これが閉じたら L-BCO2 は「答えた」になる**
- [ ] **P7** 全支持の除去 (~180 行)。**等号の前提ではなくなった** — Marton 路が外れたため。
      無制約 `martonRegionUnion` の達成側を言いたいときだけ要る。**superposition 側の対応物は S7**

**時分割 / 凸包は要らない** (在庫 §6 が実測で決着): 各 `martonRegion` は凸。union は非凸だが相手側
`bcOuterRegionUV` も非凸なので両辺が並ぶ。時分割変数 `Q` の補助への吸収は Marton では効かない
(`I(V₁;V₂)` が `H(Q)` だけ増える) が、**superposition の 2 制約領域では効く** (S6 が使う)。
凸幾何の Carathéodory は Mathlib にある (`Mathlib/Analysis/Convex/Caratheodory.lean:124` / `:149`)。
proof-log: no。

### Phase 3 — 協調外界 (安い外界) ✅

`e9222d0a` `b9ba272a`。BC 符号を 3 通り (受信機 1 のみ / 2 のみ / 協調受信) に還元し
`bcOuterRegionCoop` + `bc_capacity_subset_coop` を得た。単一ユーザー側の入口として
`channelCoding_operational_rate_le_capacity` を新設。**これで挟み込みが (緩い外界ながら) 完成**。
proof-log: no。

### Phase 4a — UV 単一文字化 (floating 形) ✅

`5bf64adf`…`54705cb3`。補助変数を `uvAux` 1 本に統一したことで identification が 2 本の
instantiation に縮んだ。核は新規自作の `csiszar_sum_identity_cond`。headline `bc_uv_converse` は
**degradedness 前提なし**。proof-log: no。

### Phase 4b — UV 外界の集合化 + 操作的包含 ✅ CLOSED

`6ddb1a48` / `bfdd55e1` `c768cc00`。headline
`bc_capacity_subset_uv : bcCapacityRegion W ⊆ bcOuterRegionUV W` (`@[entry_point]`) を**全平面版**で
達成 — 明示仮説は `W` と `[IsMarkovKernel W]` のみ。M0 在庫は
[`bc-uv-operational-inventory.md`](bc-uv-operational-inventory.md) で、S1 共有層 → S8-b 極限 + 退化
被覆まで全消化。**L-BCO4 / L-BCO5 / L-BCO6 いずれも不発動**。宣言の配置は §在庫 が SoT。

**領域定義の確定形 (Phase 5 が参照する SoT)**:

```
bcOuterRegionUV W = closure (⋃ (ν : ProbabilityMeasure (ℕ × ℕ × α × β₁ × β₂))
                               (_ : IsUVChannelLaw W ↑ν), uvRegion ↑ν)
uvRegion ν = {p | InBCOuterRegionUV p.1 p.2 (uvInfo₁ ν).toReal (uvInfo₂ ν).toReal
                    (uvInfoSum₂ ν).toReal (uvInfoSum₁ ν).toReal}
```

closure は不可避 (半平面の交差の union は閉じない) だが、それが `bcOuterRegionUV_isClosed` を
無料にし `bcCapacityRegion = closure {achievable}` との接続に効く。**第一象限制約なし** +
**下方集合** の 2 点が S8-b のコストを決めた (符号制約を入れない ⟹ 退化被覆が約 15 行。MAC が軸ごと
の片側 converse に約 420 行を要したのとの差)。`uvInfoSum₁/₂` の**下付き数字は受信機番号ではなく
「先頭に来る corner 項の選択」**(両方とも `R₁ + R₂` の上界)。
proof-log: **yes** (`docs/proof-logs/proof-log-bc-uv-operational.md`、別 dispatch)。

### Phase 5 — 一致するクラスを広げる 🚧 ★本線

degraded は既に閉じている。その一般化を、内界と Phase 4b の外界の組で回収する。

#### 定義段 ✅ (`2c938fe0` `91fd8dcf` `e6ff1963` `42ac21e7`)

M0 在庫は [`bc-phase5-class-inventory.md`](bc-phase5-class-inventory.md) (Mathlib の壁 0 件)。
`martonRegion` から `0 ≤ p.1 ∧ 0 ≤ p.2` を除去 (**これをやるまで等号はどのクラスでも述べられなかった**、
判断ログ 12) したうえで `Classes.lean` を新設し、3 クラス + 包含鎖
`degraded ⊆ less noisy ⊆ more capable` を proof done で載せた。両ゲート PASS。

#### 内外を同じ添字に載せる橋 S1–S6 ✅ (`6b0c1ea1` 在庫 / `76b83bc1` `28eae4ea` / `0186b708`)

M0 在庫は [`bc-inner-outer-bridge-inventory.md`](bc-inner-outer-bridge-inventory.md)。Marton 結合法を
外界の `ℕ` 添字に載せ、順包含 `marton_region_subset_uv` (`@[entry_point]`) まで運んだ。配置は §在庫。
**橋は `hpV` / `hK` / `hW` を 1 本も要求しない** (判断ログ 15)。予測と実測の差は判断ログ 14 / 16。
経路変更後もこの橋は**そのまま生きている** — Marton union の順包含がこれで立っているため。

#### 等号 (less noisy) 🔄 — 内界を **superposition** に差し替え

M0 在庫は [`bc-lessnoisy-equality-inventory.md`](bc-lessnoisy-equality-inventory.md) (600 行、
Mathlib の壁 0 件)。**plan が次手としていた `bcOuterRegionUV ⊆ martonRegionUnionFS` は偽**と
判定され (判断ログ 18、[`bc-facts.md`](bc-facts.md))、目標を superposition 内界に差し替えた。

到達目標:

```lean
@[entry_point]
theorem bc_lessNoisy_capacity_eq_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hln : IsBCLessNoisy W) :
    bcCapacityRegion W = bcOuterRegionUV W
```

`hW` は `bc_achievability_of_rate_lt` の regularity 前提として**逆包含側だけ**に要る (順包含
`bc_capacity_subset_uv` は無条件)。`IsBCLessNoisy` は両領域を一切参照しないチャネルレベルの述語
なので load-bearing ではない。

##### S0–S2 ✅ 全段 proof done (`06817339` 実装 / `32385115` honesty / `a97fde13` style)

| step | 成果 |
|---|---|
| **S0** 達成側の共通形への factor out | `Achievability/Assembly.lean` に `bc_ceil_exp_max_zero:1080` / `bc_Ec_lt_of_clamped_rate:1090` / **`bc_achievability_of_rate_lt:1103`** (旧 `bc_achievability` の本体。**レートの符号制約を撤廃**し `hJlt : max R₁ 0 + R₂ < bcInfoJoint` で受ける) / `bc_achievability_of_infoJoint_ge:1239` (`hsum` 形)。**`bc_achievability` の署名・結論は逐語不変** (監査が `#check` 出力のバイト一致で機械確認) |
| **S1** less noisy への接続 | `SuperpositionRegion.lean` 新設 (`InformationTheory.lean` 登録済)。`bcInfo₁_nonneg:50` + `@[entry_point]` `bc_lessNoisy_achievability:84` (本体 1 行 = `bc_achievability_of_infoJoint_ge` + `bc_lessNoisy_infoJoint_ge`) |
| **S2** 内界の集合化 | def `bcSuperpositionRegionFullSupport:119` + `@[entry_point]` `bcSuperpositionRegionFullSupport_subset_capacity:130` (仮説は `hW` + `hln` のみ)。⟹ **less noisy の言葉で `bcSuperpositionRegionFullSupport ⊆ bcCapacityRegion ⊆ bcOuterRegionUV` が並んだ** |

ゲート: honesty **all OK** (`hsum` / `hJlt` は precondition と判定。条件が残る公開宣言はゼロで、
`_of_` 接頭により条件性が名前に出ている) / style **PASS**。命名は `FS` ではなく `FullSupport` を
使い、§後続作業 F-6 の判定を新規側で先取りした (既存 `martonRegionUnionFS` 系 3 本のリネームは
follow-up のまま)。

##### S3–S8 📋 逆包含 (在庫 §推奨する次手 が SoT、合計 ~780 行)

証明戦略 (擬似 Lean、在庫 §Q2 が導出):

```
antisymm
  ├ ⊆ : bc_capacity_subset_uv W                             -- 既存、無条件
  └ ⊇ : intro ν hν p hp                                     -- p ∈ uvRegion ν
        b := (uvInfo₂ ν).toReal ; a := (uvInfoSum₂ ν).toReal - b   -- I(U;Y₂) / I(X;Y₁|U)
        U_m := 有限量子化 ; b_m ≥ b - ε_m ; a_m ≥ a                 -- S5
        I(X;Y₁) ≥ I(U_m;Y₁) + a_m ≥ b_m + a_m                      -- hln at U_m + 連鎖律
        λ := p.2 / b_m ; U' := Bool × U_m                          -- S6 時分割
        bc_lessNoisy_achievability at (p.1-δ, p.2-δ) → closure      -- S2
```

- [ ] **S3** 情報量スロットの同定 3 本 (`bcInfo₁/₂/Joint` ↔ `condMutualInfo` / `mutualInfo` の
      `.toReal`)。在庫は ~90 行としたが**下方修正** — 在庫が「自作」とした平坦↔入れ子の再ラベル橋は
      一般形 `entropy_measurableEquiv_comp` (`Shannon/Pi.lean:36`) が既存で、
      `MeasurableEquiv.prodAssoc.symm` を渡すだけで通る (S1 の `bcInfo₁_nonneg` で実証済。
      在庫が挙げた `wz_entropy_map_injective` の上流移動は**不要**)。more capable でも使う
- [ ] **S4** `IsUVChannelLaw` から Markov 鎖 2 本 (`U → X → Y₁` / `V → X → Y₁`) + `ν` の 4 つ組法の
      同定 (~140 行)。入口は `isUVChannelLaw_iff` (`Region.lean:125`)。**既存補題は 0 件**
      (`rg 'IsMarkovChain' OuterBoundUV/` 実測。`MartonBridge.lean:307` / `:333` は Marton 専用)
- [ ] **S5** 有限量子化 `U_m` + 裾評価 `I(U;Y₂ ∣ U_m) ≤ P(U ≥ m) · log |β₂|` + `a_m ≥ a` (~160 行)。
      部品は `entropy_le_log_card` + `condMutualInfo_compProd_fst_eq_lintegral` で全部既存。
      **条件付き less noisy は要らない** (ε 版で足りる)。**量子化 → less noisy の順に固定**
- [ ] **S6** 時分割の補助への吸収 (`Bool × U_m`) と 2 本の混合等式・不等式 (~180 行)。効くのは
      汎用の混合法 3 本 (`CondMutualInfoMixture.lean:102` / `:142` / `:164`) と「索引を補助の第 1
      成分に埋めて `tag` で復元する」設計パターンの 2 点で、**`bcUVTimeShare` の写経ではない**
      (あれは `BroadcastCode` の文字添字 `Fin n` 一様混合に張り付いており重み `λ` を取れない)
- [ ] **S7** 全支持への摂動 (`(1-δ)·law + δ·uniform` の連続性、~120 行)
- [ ] **S8** 逆包含 `bc_uv_subset_superposition` の組み立て + headline 等号 (~90 行)。
      凸結合の場合分け (`λ = R₂ / b` と `R₂ ≤ 0`) は probe B で機械確認済 (`nlinarith` 2 発)

**退化点 `(0,0)`**: `bc_achievability_of_rate_lt` は符号制約を持たないので S2 で既に吸収済
(`bcInfo₁_nonneg` + `max (p.1-ε) 0` の評価)。在庫が予告した 15 行の穴埋めは**不要になった**。

##### 残る 2 クラス 📋

- [ ] **more capable** (El Gamal 1979) — **「単純化」ではなく「形が違う」**。制約は 4 → 3 に減るが、
      うち 1 本 `R₁ + R₂ ≤ I(X;Y₁)` は**補助変数を含まない**新しい形で、`InBCCapacityRegion`
      (2 field) では受けきれず **3 field の新 structure が要る**。UV の `uvInfoSum₁` の
      `V = X` 特殊化で到達可能ではある。S3 / S4 はそのまま再利用できる
- [ ] **semi-deterministic** (Marton 1979) — 定義は入ったが**内界の定理が適用できない**
      (全支持仮説を定義上必ず破る、判断ログ 13) ⟹ 等号は **L-BCO7** で defer し外界側だけで止める。
      ⚠ superposition 路に移った今、L-BCO7 の判定対象は `marton_achievability` ではなく
      `bc_achievability_of_rate_lt` の `hpU` / `hK` / `hW` に移る (発動判定はこの 3 本で行う)
- [ ] **degraded との接続は「新規配線の作成」**。`bc_converse` / `bc_achievability` はどちらも
      direct consumer 0 件で合流先の配線が存在せず、`bc_converse` の degradedness は `h_deg_block`
      (ambient 上の per-letter Markov 鎖) なので **4b の橋はそのままでは効かない** (判断ログ 11-(n))

proof-log: 定義段 / 橋 S1–S6 / S0–S2 は no。**等号 (S3–S8) が閉じたら yes** — 書くべき要点は
判断ログ 18 (内界の選択がクラスごとに変わる) と S5 / S6 の量子化 + 時分割。

## 後続作業 (Phase 5 の前提ではない)

style / honesty ゲートが提起して当該 leg では見送った項目。完了したものは 1 行 + commit に圧縮して
残す (項目番号は他文書が参照するので付け替えない)。

### A. `Assembly.lean` の二段分割 ✅ 完了

`210b7558`…`3af79fea`。Assembly 1588 → **851 行**、全ファイルが 1500 行ガイド内。純粋な移設で
新しい数学は 0 行 / 新規 sorry 0 / `@audit:ok` は逐語保存。予測と実測の差は判断ログ 11-(h)(i)(j)。

### B. 命名 / 死んだ宣言 (**波及がほぼ 0 の今なら事実上無料**)

1. **`bc_uv_rate_extract` (`Bridge.lean:602`、`@audit:ok`) が dead** — Assembly が
   `bc_uv_converse_slots` に乗り換えた結果 direct consumer **0**。削除 or 保持の判断が要る
2. **`*_point_mem` 5 本の命名** (`Assembly.lean` `:429` / `:565` / `:609` / `:635` / `:696`) —
   形容詞が段階を系統的に区別しておらず名前だけでは判別不能。`docs/rules/naming.md` §2 は判別子を
   仮定側に置けと定める (`bc_uv_mem_of_letterSum_le` 等)。**波及ほぼ 0**
3. `uvAux_pad_mutualInfo_prod_eq` (`Bridge.lean:723`) の `prod` が何の直積か名前から読めない。
   `uvAux_pad_pair_mutualInfo_eq` 等へのリネーム提案。consumer は in-file 1 件
4. **命名の軽微な逸脱** `condMutualInfo_eq_of_leftInverse_cond` (`CondMutualInfoMixture.lean:66`) —
   区別子 `_cond` は `_of_` の**前**が Mathlib 順。単独のリネーム leg になる。優先度低

### C. 数学的な締めどころ / その他

1. **`bcConverseFanoSlack₁_le` が 2 bit 捨てている** — `Real.log (M₁ - 1) ≤ Real.log M₁` への緩和。
   converse の結論には効かないが、将来レートの残差を詰めたくなったときの最初の締めどころ
2. `bcOuterRegionUV ⊆ bcOuterRegionCoop` を示せれば「UV は協調外界より狭い」が機械可読になる (**任意**)
3. `CodeToAmbient.lean` の無タグ 7 本。file 全体のタグ被覆を揃えるなら別 leg。同ファイルに
   `show` → `change` の linter 警告が 1 件 (`lake build` でのみ出る)
4. **section 再配置による逐語コピーの完全畳み込み (残 ~30 行)** —
   `∑ i, uvInfo₁ (bcUVJointDistribution c W i)` 形への畳み込みは現配置では不可能
   (`bcUVJointDistribution` は `uvAuxPad` に依存し、`uvAuxPad` は `bc_uv_converse_from_code` より
   **後ろ**)。取りに行くなら `section Pad` + `section PerLetterInfo` の上方移動が要る
5. **規約どうしが同じケースで逆方向に引く件 (本 plan の範囲外・記録のみ)**:
   `docs/rules/docstrings.md` item 1 (`## Main statements` 掲載定理には docstring 必須) と
   `scripts/lean_doc_lint.ts` の `internal-doc` ratchet (`:476`) が構造的に衝突する。リンターは
   module doc を見ず `@[entry_point]` かタグ持ちだけを headline と見なすので、隙間に落ちた宣言に
   散文 docstring を足すと 1 本あたり ratchet +1 で `--check` が落ちる。**分割は衝突を再生産する**。
   解は「真の headline に `@[entry_point]` を付ける」か「現行慣行を追認する」の二択 = 人の判断で、
   起票先は `docs/rules/` 側。**前者を実践した事例が `Classes.lean` / `MartonUnion.lean` /
   `SuperpositionRegion.lean`** — Main statements 掲載分すべてに `@[entry_point]` が付き ratchet
   寄与 **0**。新規ファイルを切るときの既定手として使える

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
   4 本で、残り 3 本は**再符号化不変性**で mixture に一切触れない。決定的な tell:
   **`Bridge.lean` は本ファイルを `mutualInfo_eq_of_leftInverse` のためだけに import している**。
   分割案 = `Shannon/MutualInfoReencoding.lean` (再符号化 3 本) + 現ファイル (mixture 4 本)。
   consumer が既に綺麗に分かれているので循環なし。着手時は判断ログ 11-(i) を先に適用すること
2. **`open scoped BigOperators` が tree 全体で死んでいる** — 同じ open を持つファイルが **189 本**
   あり数ファイルだけ外すと不揃いになる。tree 一括 sweep として別 leg にするのが筋で
   **本 plan の範囲外**

### F. Phase 5 / Phase 2 / S0–S2 が新たに立てた flag

1. **`bcJointDistribution_id_eq` (`Classes.lean:166`) のリネーム (「今が最安」)** — 裸の `_eq` で
   右辺が名前に出ず、内部橋なので docstring も無い。**consumer は同ファイル内 1 箇所のみ**。代案
   `bcJointDistribution_id_eq_map_compProd`。「1 行 docstring を足す」路は §C-5 の ratchet で落ちる
2. `bc_lessNoisy_infoJoint_ge` (`Classes.lean:95`) / `bc_degraded_infoJoint_ge`
   (`Achievability/Assembly.lean:967`) の `_of_` 化 — 厳密形は `bc_infoJoint_ge_of_lessNoisy`。
   **2 本同時リネームか両方現状維持かの二択** (style の推奨は現状維持)
3. 語彙橋 2 本を `private` にするか。優先度低
4. `IsBCSemiDeterministic.exists_prob_real_singleton_eq_zero` に `_of_one_lt_card` を付けるか (任意)
5. **README 定理表への登録は保留** (オーケストレーター判断) — 包含鎖は headline としては弱く、
   等号が閉じた段で登録するのが自然。`docs/readme-theorems.txt` は未編集。**判断待ち**:
   `marton_region_subset_uv` / `bcSuperpositionRegionFullSupport_subset_capacity` は等号ではないが
   `bc_capacity_subset_uv` と対になる強さの `@[entry_point]` ⟹ **等号を待たず登録してよいか**
6. **リネーム束 — 4 本まとめて 1 leg**。いずれも**外部 consumer 0** (`rg` 実測) = 今が最安。
   - `auxNatIndex` → `natIndex` (推奨度 中) — 定義は任意の `Fintype X` に総称で、「補助変数の」は
     使用側のラベルにすぎない。Mathlib 慣行の `aux` = 繋ぎ宣言とも読める
   - `martonSwapLaw` → `martonAuxSwapLaw` (推奨度 低) — 何を swap したのかが名前に出ていない
   - **`martonInfoSum` が実在しない識別子** (推奨度 低) — `MartonBridge.lean:493` / `:509` の左辺は
     def として存在せず実体はベタ書き ⟹ 読者が grep して空振りする。解消は (a) `Marton/Setup.lean`
     に `def martonInfoSum` を新設、(b) リネーム、の二択
   - **`FS` 略記 → `FullSupport`** (推奨度 高、**未実行**) — `martonRegionUnionFS` /
     `_FS_subset_union` / `_FS_subset_capacity` の 3 本。`rg` 実測で `FS` を宣言名断片に使うのは
     tree 全体でこの 3 本のみ (**先例ゼロ**)。**新規側 (`bcSuperpositionRegionFullSupport`) は
     既に展開形を採用済**なので、直すのは既存 3 本だけ = 綴りの不統一が今まさに存在する状態

   **束に入れない判定が 2 件**(蒸し返し防止): (a) **`bcAuxAlphabet` は別の束** — ここでの `Aux` は
   **教科書用語の auxiliary random variable** で、同族の descriptive 先例が 4 本。弁別軸は「総称なのに
   補助を名乗る (over-claim)」か「補助としてしか使われない」か。(b) **`martonRegionUnion_subset_uv` は
   family 既定と食い違っていない — 逆に既存 2 本が outlier** — `marton_region_subset_uv` /
   `marton_region_subset_capacity` だけが def 名を割っていて **def 名で grep すると引っかからない**。
   統一するなら直すのは古い 2 本だが、両方 `@[entry_point]` + 実 consumer あり ⟹ 別 leg。優先度低
7. (旧項目は F-6 のリネーム束に統合)
8. (**§C-5 に統合**)
9. **`docs/rules/lean-style.md:29` が repo 実態と矛盾** (**本 plan の範囲外・記録のみ**) —
   「演算子は行末に置いて改行する」は複数行シグネチャの**関係記号**には当てはまっていない。継続行を
   関係記号で始める行は tree 全体で **約 5800 行 / 353 ファイル** (実測)。起票先は `docs/rules/` 側
10. **`Achievability/` クラスタ 4 ファイルの module doc タイトルが実態とずれた** (S0–S2 の style
    ゲートが提起、**未実行**) — いずれも "Degraded broadcast channel — …" のままだが、S0 で assembly は
    **degradedness 非依存**になり、実際 `SuperpositionRegion.lean` が less noisy から消費している。
    4 ファイル同時のクラスタ一貫性判断なので単独では直さず flag
11. **`bc_lessNoisy_achievability` の docstring が共有コアとして `bc_achievability` を名指している**
    が、実際に共有されているのは `bc_achievability_of_infoJoint_ge` (S0–S2 の style ゲート)。
    偽ではないので未修正、優先度低

以下 3 件は橋 S5 / S6 の style ゲートが提起し、**いずれも未実行**。

- **F-a: `isMarkovChain_map_comp` (`MartonBridge.lean:264`、private、15 行) を
  `CodeToAmbient.lean` の `### Information transport under a shared pushforward` 節 (`:430`–`:520`)
  へ上流移動** — 同節の 4 本と名前の形・型変数レイアウト・引数順が完全に同族で、同節の
  `condDistrib_map_comp` を直接消費している。**import 書換ゼロ**。⚠️ 移動先で docstring を付けると
  `internal-doc` ratchet が +1 になる (§C-5 と同一の軸)
- **F-b: `mutualInfo_le_add_condMutualInfo` (`MartonBridge.lean:357`、private、8 行) を
  `Shannon/CondMutualInfo.lean` へ上流移動** — BC 固有要素ゼロの教科書的不等式で **import 書換ゼロ**。
  **条件付き版が `OuterBoundUV/Gateway.lean:194` に public + `@audit:ok` で既存**なので、無条件版が
  private で 2 ファイル離れて埋まっている状態は「既に書いたか」失敗モードの温床
- **F-d: public / private の非対称 (API 面、人の判断待ち)** — `martonInfoV₁V₂_eq_mutualInfo_toReal:252`
  は public かつ `## Main statements` 掲載なのに、完全な兄弟 `:403` / `:414` は private

## 未解決本体との距離 (正直な見積り)

「Marton 内界 = 一般 BC の容量領域か」は **open**。数学が存在しないので形式化できない。本計画が
終わっても未解決問題は未解決のままで、得られるのは以下。

- 内界・外界・容量領域が同一言語で並び、**ギャップが機械可読な形で固定される**
- 特定の BC で内外が分離するかを検証する基盤 (反例候補の検算)。**この基盤は既に 1 度使われた** —
  判断ログ 18 の判定はまさにこの用途
- 一致が既知の特殊クラスについては、等号が実際に閉じる (Phase 5)

期待値は「厳密な足場 + 教材価値」に置くのが妥当。

## 設計上の未決事項

1. **補助変数 union の射程** (Phase 2) — **濃度固定で止める形で決着**。情報理論側の Carathéodory
   (支持補題) は書かない (Fenchel–Eggleston が Mathlib 不在ゆえ自作行数が跳ねる、在庫 §Q2-3)。
   残る判断は P7 を取るかだが、**等号の前提ではなくなった**
2. **more capable の容量領域を受ける structure** (Phase 5) — 3 制約 (うち 1 本は補助変数を
   含まない `R₁ + R₂ ≤ I(X;Y₁)`) なので `InBCCapacityRegion` を拡張するか新 structure を建てるか
3. **`martonInfo*` を `ℝ≥0∞` 版へ pivot するか** — **less noisy の等号からは外れた** (L-BCO8 の
   代替の攻め筋として書かれていたが、その L-BCO8 自体が無効化された)。superposition 路では
   `I(V₁;V₂)` (補助 × 補助) が現れず 4 スロットすべてが出力との情報量なので、`.toReal` の危険は
   構造的に発火しない (判断ログ 17 の反例 class が起きない)。⟹ **本件は Marton union の API を
   完成させたくなったときだけの判断**に降格。判断材料は `marton_achievability` への波及の実測

`uvRegion` の `.toReal` を `ℝ≥0∞` 版に移すかは**決着** — 有限アルファベットでは無関係で、判断が
要るのは `StandardBorelSpace` 側への拡張に進むときだけ。Phase 4b の 2 件も決着済。履歴は git。

## 撤退ライン (frozen slug)

| slug | 発動条件 | 退避先 |
|---|---|---|
| **L-BCO1** | Phase 4 の補助変数 identification が閉じない | **不発動** (Phase 4a で `uvAux` 1 本の 2 通り instantiation により閉じた) |
| **L-BCO2** | Phase 2 の型量化 union が universe 問題で詰む | 濃度固定版で止め、union は取らない。**不発動** (P1–P3)。問題は union の定義側ではなく**消費側** (`IsBCLessNoisy` が `U : Type u` を量化) にあり、`bcAuxAlphabet = ULift.{u} (Fin (k+1))` が **0 行で吸収**した。**P6 (付け替え不変性) が閉じたら「答えた」になる** |
| **L-BCO3** | Phase 5 の等号が Phase 4 の外界の形と噛み合わない | クラス定義だけ入れて等号は defer。**発動条件の文言は実態とずれている** — 噛み合わなさの本体は外界の形ではなく**内界の形**だった (符号制約 = `2c938fe0` で解消 / 内界の選択 = 判断ログ 18 で superposition へ / 全支持仮説 = L-BCO7)。slug は凍結なので文言はそのまま残し、判定は内界側の 3 点で行う |
| **L-BCO4** | Phase 4b の符号→ambient 橋または単一文字還元が閉じない | **不発動のまま Phase 4b が完遂** |
| **L-BCO5** | S5 の補助変数の型統一が `mutualInfo_chain_rule` 経由でも閉じない | **不発動** (在庫の攻略路がそのまま効いた)。退避先だった `bcOuterRegionUVAt W n` + `⋂ n` 版は採らない |
| **L-BCO6** | S8-b の退化レート被覆が MAC 同様 450 行級に膨らむ | **不発動** — `bc_capacity_subset_uv` は**全平面版**で closure した (退化被覆は約 15 行 + `2 ≤ M` の穴埋め 55 行) |
| **L-BCO7** | semi-deterministic の等号を狙う段で、内界の達成側の全支持仮説が外せない (判断ログ 13) | **semi-deterministic はクラス定義 + 外界側だけで止め、等号は述べない**。外界 (`bc_capacity_subset_uv` の特殊化) は `hW` を要求しないので単独で成立する。退避の出口は `sorry` + `@residual(plan:bc-semideterministic-fullsupport)`。**`IsSemiDeterministicAchievable` のような述語に核を束ねる形は取らない**。**判定対象は経路変更で移った** — 旧: `marton_achievability` の `hW` / 新: `bc_achievability_of_rate_lt` の `hpU` / `hK` / `hW` (superposition 路)。橋 S1–S6 は全支持仮説を 1 本も要求しない (判断ログ 15) ので本ラインの外 |
| **L-BCO8** | 等号の逆包含 `bcOuterRegionUV W ⊆ martonRegionUnionFS W` を書く段で、`bcOuterRegionUV` の `ℕ` 補助を `martonInfo*` の `[Fintype]` 要求に合わせられない。**⚠ 無効化 (不発動ではない)** — この逆包含は**偽**と判定された (判断ログ 18、[`bc-facts.md`](bc-facts.md))。閉塞は型でも濃度上界でもなく**目標命題が成り立たない**ことにあり、「(i) Carathéodory 型の濃度上界 / (ii) 有限量子化 + 極限回収 のどちらで開くか」という枠組みごと無効。slug は凍結なので行は残す | **⚠ 使用禁止**。旧退避先「逆包含を `sorry` + `@residual(plan:bc-marton-uv-cardinality-bound)` で署名を保つ」は**取れない** — 偽の命題を署名として残すことになる (CLAUDE.md 検証の誠実性)。同じ理由で「`martonInfo*` を `ℝ≥0∞` へ pivot する」代替の攻め筋もこのラインからは外れた (§設計上の未決事項 3)。後継は **L-BCO9** |
| **L-BCO9** | less noisy の等号で **S5 (有限量子化 + 裾評価) または S6 (時分割の補助への吸収) が閉じない** | 逆包含 `bc_uv_subset_superposition : bcOuterRegionUV W ⊆ bcSuperpositionRegionFullSupport W` を **署名を保ったまま** `sorry` + `@residual(plan:bc-lessnoisy-converse-quantization)` で残し (後継 plan のファイル名 stem)、S0–S3 の成果だけで leg を閉じる。この時点でも `bcSuperpositionRegionFullSupport W ⊆ bcCapacityRegion W ⊆ bcOuterRegionUV W` の挟み込みが **less noisy の言葉で** 1 本立つので単独で価値がある。**`IsLessNoisyTight` / `IsSuperpositionOptimal` のような「等号が成り立つ」を束ねる述語は作らない** |

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
S3 スロット同定 → S4 Markov 鎖 → S5 量子化 + 裾評価 → S6 時分割 → S7 全支持摂動 → S8 逆包含 + 等号
  ↓                                                     (詰んだら L-BCO9)   ★次の一手は S3
more capable の等号 (3 field の新 structure、S3 / S4 を再利用) → semi-deterministic は L-BCO7
```

**S3 / S4 は独立に価値が出る** (more capable でも使う) ので、S3 → S4 の順で切るのが安い。
**Phase 2 の P4–P7 はいずれも等号の前提ではない** (経路変更後、P7 も外れた)。
§後続作業 B–F はいずれも前提ではない (F-1 / F-6 リネーム束のみ consumer が 0 の今が最安)。

## 判断ログ

9. **union の添字を縛る 2 条件は `IsUVChannelLaw` 1 本 = 単一の合成積恒等式で解決した (S7)**:
   `uvInfo*` は 5 つ組法 `ν` の 1 引数汎関数でチャネル `W` を引数に取らないため、union を無制約に
   取ると出力を入力にコピーする `ν` が 4 スロットを任意に大きくでき、**外界が平面全体に退化して
   `bc_capacity_subset_uv` が vacuous に真になる**。S7 は要る 2 条件を 1 本の等式で同時に課し、
   `isUVChannelLaw_iff` が「union の添字は補助と入力の任意の同時法をチャネルに通したもの ちょうど」
   を与えて反例 class ごと閉じた。監査の判定は「`IsUVChannelLaw` は load-bearing hyp ではなく
   **包含の右辺を縮める構造条件**」。**Phase 5 が外界の形を触るときは、この特徴づけが壊れないかが
   最初のチェック点** (S4 が `isUVChannelLaw_iff` から Markov 鎖を出す段で最初に当たる)。
11. **在庫予測の外れ (通算 22 件) — 在庫ファイル自体は編集しないので本エントリが記録の SoT**。
    生きた教訓のみ残す (settled な個別項目は git):
    - **(f) 雛形を参照するときは「その雛形の到達目標が自分と同じ強さか」を先に確認する** —
      「MAC の約 420 行が退化レート被覆の雛形」は誤りで、MAC はそもそも退化レートを被覆していない。
      S6 でも再発 (`bcUVTimeShare` は `Fin n` 一様混合に張り付いていて重み `λ` を取れない)。
    - **(g) 前 step の到達点が次 step の入口として使えるとは限らない** — 縮小点の**加法形**は極限に
      乗らない。**乗法形**への差し替えで解決。step 境界では結論の**形**を独立に確認する。
    - **(i) import の必要性は consumer 表ではなく移動先の依存の閉包で決まる** (分割 A の 3 件)。
    - **(k) 「独立」「park 可」の判定は到達目標ごとに違う** — park 判定は目標を名指して書く。
      ⚠ この判定自体が経路変更で覆った: Phase 2 は「等号の前提」だったが、内界が superposition に
      移って**前提ではなくなった** ⟹ 依存関係の宣言は「どの目標に対して」を明示しても、**目標側が
      差し替わると失効する**。
    - **(l) more capable は「単純化」ではなく「形が違う」+ 文献帰属が 1 件誤り** — less noisy は
      **Körner–Marton 1975/1977** (El Gamal 1979 は more capable)。制約は 4 → 3 に減るのに
      `R₁ + R₂ ≤ I(X;Y₁)` が補助変数を含まない新形ゆえ受け皿の structure は新設が要る。
    - **(m) `.toReal` の危険の向きが逆だった** — `⊤ ↦ 0` は外界を**縮める**ので逆包含では保護側。
      ⚠ **この判定は外界についてのみ正しい** — 内界を `ℕ` 補助に載せると発火する (判断ログ 17)。
    - **(n) 「同じ floating 形だから橋が効く」は形の一致であって仮説の一致ではない** —
      `bc_converse` の degradedness は `h_deg_block` で、対応版は 0 hit、新規 ~120 行が要る。
      再利用可否は結論形ではなく**要求される仮説の表現**で決まる。
12. **片側で採った規約変更は、対になるもう片側にも適用したか確認する (`2c938fe0` で解消)**:
    「外界に第一象限制約を入れない」判断を内界に適用する step が無く、`martonRegion` だけが第一象限の
    まま残って `bcOuterRegionUV ⊆ martonRegion` は**どの `W` でも偽**だった。⟹ **規約 (符号制約・
    座標順・`ℝ` / `ℝ≥0∞` の別) を片側で変えたら、対になる側との差分を必ず 1 度取る**。
13. **semi-deterministic は内界の定理と構造的に非両立 (L-BCO7 の根拠)**: `marton_achievability` の
    全支持仮説 `hW : ∀ a b, 0 < (W a).real {b}` を **semi-deterministic は定義上必ず破る**
    (`Y₁ = f(X)` なので到達しない出力対の質量が 0)。in-tree の証拠は
    `IsBCSemiDeterministic.exists_prob_real_singleton_eq_zero`。⟹ 一般教訓: **「文献で容量領域が
    既知」と「in-project の内界定理が適用できる」は別**。クラスを候補に挙げる前に、そのクラスが
    **既存定理の regularity 前提と両立するか**を先に見る。⚠ superposition 路でも全支持は要る
    (`hpU` / `hK` / `hW`) ので、この非両立は内界を差し替えても解消しない。
15. **橋は内界側の全支持仮説を 1 本も要求しない ⟹ L-BCO7 は緩む方向 (S1–S6 を通じて不変)**:
    明示仮説は `pV` / `K` / `W` と型クラスだけで、`hpV` / `hK` / `hW` は 1 本も現れない (署名走査で
    実測)。⟹ 一般教訓: **撤退ラインは「どの宣言が止まるか」まで降ろして書く**。「クラス X では
    内界が使えない」の粒度だと、無関係な後続 step まで巻き込んで park することになる。
16. **在庫が「無いので自作する」と書いた資産は、実装着手時に両方の検索軸で引き直す (2 回発火)**:
    (a) 橋 S5 — 「条件付き DPI は in-project に無いので 5 step で挟む」は誤りで
    `condMutualInfo_le_of_markov_joint` (`ConverseMemorylessChainRule.lean:113`) が要求どおりの形で
    存在し、核は **8 行 × 2** に縮んだ。当てたのは**名前検索**で、結論形検索では出なかった。
    (b) S0–S2 — 「平坦↔入れ子の再ラベル橋は WynerZiv 配下にしかないので上流移動か自作」も誤りで、
    一般形 `entropy_measurableEquiv_comp` (`Shannon/Pi.lean:36`) が既に import 閉包内にあり
    `MeasurableEquiv.prodAssoc.symm` を渡すだけで通った ⟹ **S3 の ~90 行見積りは下方修正**。
    ⟹ 一般教訓: **在庫段階の 0-hit は検索軸に依存する**。CLAUDE.md「in-repo asset search」の
    結論形検索だけでは構造的に見えない資産がある (名前検索と両方要る)。
17. **内界を `ℕ` 補助に載せる設計は反例で潰れた (Phase 2)**: 外界と同じ `ℕ` 添字の 5 つ組法に内界も
    載せれば橋が要らなくなる、という設計は**順包含が偽になる**。反例は `W a = dirac (a, a)` で、
    `H(N) = ∞` の `N` を両補助へ詰めると `I(V₁;V₂) = ⊤ ⟹ .toReal = 0` で和レートの罰則項が消える。
    **構造的理由**: 外界の 4 スロットは全部**出力との**情報量なので有限出力なら自動的に有限だが、
    **内界の `I(V₁;V₂)` だけが補助 × 補助**。⟹ 一般教訓: **同じ変換 (`.toReal`) の安全性は、それが
    載る汎関数の引数がどこから来るかで決まる**。superposition 路では `I(V₁;V₂)` が現れないので
    この反例 class は構造的に起きない (ルート変更の副次的な利得)。
18. 🔄 **内界の選択はクラスごとに変わる — `martonRegionUnion` は劣化 BSC 対ですら容量領域より真に
    小さい (経路変更、在庫 §Q1)**: plan が「等号に残る唯一の包含」としていた
    `bcOuterRegionUV ⊆ martonRegionUnionFS` は**偽**。劣化 BSC 対 (`q=0.1`, `p=0.25`) の
    superposition corner 点は `bc_capacity_subset_uv` により外界に入るが、`martonRegionUnion` の
    3 制約の最小スラックが補助アルファベット `(2,2)`〜`(5,5)` で一様に約 `-0.013` に頭打ちし
    closure でも跨げない (union の任意の点との距離 ≥ `0.0129/√2`)。sim は Lean の def から逐語対応
    させ閉形式 5 項目と 10 桁一致で検証済、退化境界 2 本 (`Y₁` 無雑音 / `b=0`) でスラックちょうど 0 と
    いう予測どおりの挙動も確認 (詳細と再検証コマンドは [`bc-facts.md`](bc-facts.md))。
    **より重い含意**: corner 点は `bcCapacityRegion` に入るので **劣化 BSC 対ですら
    `martonRegionUnionFS ⊊ bcCapacityRegion`**。原因は `martonRegionUnion` が EGK Thm 8.3 の共通補助
    変数 `U₀` を持たない形であることで、`U₀` は `martonRegion` の署名に**入る余地がない** (足すのは
    `marton_achievability` の符号化定理からの作り直し = Phase 5 の射程外)。時分割の補助への吸収も
    Marton では効かないので凸化でも埋まらない。⟹ 内界を superposition に差し替え、L-BCO8 を無効化し
    L-BCO9 を新設した。⟹ **一般教訓 2 つ**: (a) **plan が「⚠ 正直な限界」として書いた但し書きは、
    最も素直なクラスで実際に発火しうる** — 限界を書いた時点で「どのクラスで発火するか」まで詰めて
    おかないと、その但し書きの下流に建てた目標が丸ごと偽になる。(b) **「内界 ⊆ 容量領域」の 1 本を
    持っていることは「その内界で等号が狙える」を意味しない** — 等号の相手として使う前に、既知の
    到達点 (ここでは superposition corner) がその内界に入るかを 1 度数値で当たる。
