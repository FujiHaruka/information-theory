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
- [ ] Phase 4b UV 外界の集合化 + 操作的包含 📋 ★現在の本線
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
| `uvAux` | `OuterBoundUV.lean:71` | UV 補助変数。`Uᵢ = uvAux W₂ …` / `Vᵢ = uvAux W₁ …` |
| `bc_uv_singleletterize_r1/_r2/_sum₁/_sum₂` | `OuterBoundUV.lean:113` / `:174` / `:684` / `:637` | 単一文字化 4 本 (corner 2 + sum-rate 2)、degradedness 前提なし |
| `InBCOuterRegionUV` / `bc_uv_converse` | `OuterBoundUV.lean:735` / `:815` | UV 外界の 4 不等式束と メッセージレベル headline (`@[entry_point]`) |
| `csiszar_sum_identity_cond` | `OuterBoundUV/Gateway.lean:246` | 条件付き Csiszár 和恒等式 (異アルファベット + 背景 conditioner)。Phase 4a の核 |
| `csiszar_sum_identity` | `BroadcastChannel/ConverseGateway.lean:142` | 無条件版 (同一アルファベット) |
| `bc_converse` / `bc_input_singleletterize` | `BroadcastChannel/Converse.lean:571` / `:316` | degraded 限定の converse。Phase 5 の接続先。**これも floating 形** |
| `bc_achievability` | `BroadcastChannel/Achievability/Assembly.lean:1093` | degraded 限定の達成側。Phase 5 の接続先 |
| `marton_achievability` | `Marton/Achievability.lean:767` | 一般 BC 内界 (EGK Thm 8.3、private message のみ) |
| `InMartonRegion` | `Marton/Basic.lean:40` | 3 不等式バンドル (点ごと述語) |
| `MACAchievable` / `macPentagon` / `macCapacityRegion` | `MultipleAccess/TimeSharing.lean:49` / `:58` / `:66` | 操作的述語 → closure で集合化のパターン |
| **MAC の符号→ambient 橋** | `MultipleAccess/TimeSharingConverse/Bridge.lean` (1238 行 / 48 decl) | **Phase 4b の唯一の雛形**。`macConverseAmbient:348` → `mac_converse_from_code:777` → `mac_converse_rate_extract:854` → per-letter 情報量の同定 `:1109`–`:1214` |
| `mac_avgPentagon_mem_convexHull` | `Bridge.lean:94` | n 文字平均を単一文字分布の凸包へ落とす先例 |
| `mac_capacity_region_reconciliation` | `MultipleAccess/Reconciliation.lean:292` | 内外を同じ言語に揃える先例 |

**存在しないもの**: `bcOuterRegionUV` (UV 外界の集合版) と `bc_capacity_subset_uv`。BC 符号から
ambient 確率測度を構成する橋 (MAC の `Bridge.lean` 相当が BC 側に無い)。less noisy / more capable /
semi-deterministic のクラス定義 (project 全体で 0 hit)。

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
  構成する橋と、n 文字の平均を単一文字分布へ落とす凸化。情報量の議論は一切増えない。

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

### Phase 4b — UV 外界の集合化 + 操作的包含 📋 ★本命・最重量

到達目標は `bcOuterRegionUV W : Set (ℝ × ℝ)` と
**`bc_capacity_subset_uv : bcCapacityRegion W ⊆ bcOuterRegionUV W`**。

- [ ] **M0 在庫**: MAC の `Bridge.lean` を `CodeToAmbient` / `RateExtract` / `PerLetterInfo` の 3 節に
      分けて読み、BC への読み替え対応表を作る (1 出力 → 2 出力、2 送信者 → 1 送信者 2 メッセージ)。
      **ここで初めて 4b の行数が読める**。現時点の見積りは「MAC 実績 1238 行 / 48 decl と同等以上」
      という外挿しか無い
- [ ] **符号 → ambient**: 独立一様 2 メッセージ → encoder → BC カーネルの compProd で `μ` を構成
      (`macConverseAmbient` 相当)。`IsProbabilityMeasure` インスタンス群まで
- [ ] **構造前提の導出**: `bc_uv_converse` が要求する `h_memo₁` / `h_memo₂` / `hmarkov₁` / `hmarkov₂` /
      `h_indep` / 一様性 2 本を、構成した `μ` から導く (`macConverse_memorylessChannel` /
      `macConverse_mutualInfo_eq_zero` / `macConverse_isMarkovChain` 相当)。**下記「結合 Markov」の
      申し送りが効くのはここ**
- [ ] **レート抽出**: `Real.log (Fintype.card ξₖ)` を `n · Rₖ` の下界に変換 (`le_log_of_ceil_exp_le` /
      `mac_converse_rate_extract` 相当) し、Fano slack を誤り確率 → 0 の列に沿って消す
- [ ] **単一文字分布への還元**: n 文字の平均を単一文字補助変数の分布に落とす。MAC は
      `mac_avgPentagon_mem_convexHull` で凸包へ逃がした。**4b の第二の難所**で、時間共有変数を
      補助変数に吸収する標準手法を Lean 化する必要がある
- [ ] **集合定義**: `bcOuterRegionUV W : Set (ℝ × ℝ)` を単一文字補助変数分布についての union +
      closure で定義。**第一象限制約は入れない** (下記 判断ログ 1)
- [ ] `bc_capacity_subset_uv` の組み立て + `bcOuterRegionUV_isClosed`
- [ ] `bcOuterRegionUV ⊆ bcOuterRegionCoop` を示せれば「UV は協調外界より狭い」が機械可読になる
      (**任意**。示せなくても挟み込みは 2 本並立で成立する)

**4b への申し送り (Phase 4a の独立監査が特定)**: `h_memo₁` / `h_memo₂` は各出力を**個別に**条件付き
独立にするだけで、出力**対**についての結合 Markov 連鎖を含意しない (座標ごとの条件付き独立は結合の
条件付き独立を導かない)。`bcOuterRegionUV` を単一文字分布上の集合として定義する段では結合形が要る
ので、(a) 構造前提を結合形に強めるか、(b) 操作的 wrapper 側で `μ` の構成から導くか、の判断が発生
する。**操作的構成では成立するので数学的障害ではなく仮説の形の問題**であり、(b) が既定。

**(a) を選んだ場合の波及 (`scripts/dep_consumers.sh` で機械確認)**: `h_memo` を仮説に取る decl は
6 本 (`uvAux_markov_of_memo` / `bc_uv_input_step` / `bc_uv_input_step'` /
`bc_uv_singleletterize_sum₂` / `bc_uv_singleletterize_sum₁` / `bc_uv_converse`)。`bc_uv_converse` の
direct consumer は 0 decl、単一文字化 4 本の direct consumer は各 1 decl (= `bc_uv_converse`)、
`uvAux` の direct consumer は 11 decl。**すべて `OuterBoundUV.lean` 1 ファイル内**なので、
署名変更の blast radius は他家系に漏れない。

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

proof-log: 未定 (クラス定義段は no、等号が閉じたら yes)。

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
2. **単一文字還元の形** (Phase 4b) — 時間共有変数を補助変数に吸収するか、MAC のように凸包へ
   逃がすか。前者は `bcOuterRegionUV` が単一の union で書けて後者は凸包演算が残る
3. **結合 memoryless を仮説側と構成側のどちらで持つか** (Phase 4b、上記申し送り)

## 撤退ライン (frozen slug)

| slug | 発動条件 | 退避先 |
|---|---|---|
| **L-BCO1** | Phase 4 の補助変数 identification が閉じない | **不発動** — Phase 4a で `uvAux` 1 本の 2 通り instantiation により閉じたため、Körner–Marton / Sato への後退は不要になった |
| **L-BCO2** | Phase 2 の型量化 union が universe 問題で詰む | 濃度固定版で止め、union は取らない (Phase 3–5 は影響を受けない) |
| **L-BCO3** | Phase 5 の等号が Phase 4 の外界の形と噛み合わない | クラス定義だけ入れて等号は defer |
| **L-BCO4** | Phase 4b の符号→ambient 橋または単一文字還元が閉じない | `bcOuterRegionUV` の集合定義までは入れ、`bc_capacity_subset_uv` を `sorry` + `@residual(plan:bc-general-region-plan)` で残す。橋を別 plan に切り出す場合は新 plan の filename を slug に合わせて `@residual(plan:<新 stem>)` に張り替える。**4a の floating 形 headline は無傷で残るので、退避しても到達済の成果は減らない** |

**禁止事項**: どの撤退でも「外界が成立する」「補助変数が取れる」「符号から ambient が取れる」等を
`*Hypothesis` 述語に束ねて仮説として渡す形は取らない (CLAUDE.md 検証の誠実性 tier 5)。退避は
`sorry` + `@residual` で、署名は証明したい形のまま保つ。特に Phase 4b では、結合 memoryless を
「操作的構成から導けなかったので仮説で受け取る」と書き換えるのは、**それ自体は構造前提として
honest でありうる**が、`bcCapacityRegion ⊆ …` の左辺が符号を量化している以上、包含の主張から
仮説へ核が移動する形になっていないかを毎回確認する。

## 推奨実行順

**4b → 5**。Phase 2 は独立で、いつ入れてもよいし入れなくても本線は完結する。Phase 5 のクラス定義
だけは 4b と並行して着手できるので、4b の M0 在庫が重いと判明した時点で先に入れる手もある。

## 判断ログ

1. **外界に第一象限制約を入れない**: `bcCapacityRegion` は**非正レート対を真に含む** (単一メッセージ
   符号で達成可能、Phase 1 の独立監査が特定)。外界に `0 ≤ R` を入れると包含が偽になる。Phase 3 は
   符号制約も入れない形を採り、レート上界が任意の実数レートで成立するため左辺との交差も不要だった。
   **`bcOuterRegionUV` の定義でも同じ制約が効く** (容量は非負なので非正部分は損失にならない)。
2. **Phase 4 を 4a (情報量レベル) / 4b (操作的レベル) に分割**: Phase 3 は Wolfowitz strong converse
   の対偶で ambient 構成を迂回できたが、Fano ベースの UV 外界では同じ手が使えない。難所が「Csiszár
   の適用形」と「符号→ambient の橋 + 凸化」で別物であり、前者だけでも独立した到達点になる。
   degraded 版 `bc_converse` も floating 形なので、4b の橋は 2 箇所に効く共有資産。
3. **座標ごと条件付き独立は結合の条件付き独立を導かない** (Phase 4a 独立監査): `h_memo₁` / `h_memo₂`
   は各出力を個別に条件付き独立にするだけ。4b で単一文字分布上の集合を定義する段では結合形が要る。
   既定は「操作的 wrapper 側で `μ` の構成から導く」で、仮説強化は代替案。
4. **Phase 5 の等号は Phase 4b が事実上の前提**: semi-deterministic BC の等号は内界と外界を同じ言語
   で比較する必要があり、4a の floating 形では `martonRegion` と並べられない。ただしクラス定義の
   新設 (less noisy / more capable / semi-deterministic) は 4b と独立に進む。
