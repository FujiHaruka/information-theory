# Shannon: 一般 BC 容量領域フレーム サブ計画

> **Parent**: [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md) §L-BC5 後続

未解決問題「一般 2 受信者 BC の容量領域の特徴づけ」に対して形式化が提供できるのは **足場**
(内界 / 外界 / 両者による挟み込み) までで、未解決本体 (内外一致) は数学が存在しないので Phase 外。
本計画はその足場を組む。到達目標は `martonRegion W ⊆ bcCapacityRegion W ⊆ bcOuterRegion W` を
Lean の 1 本の定理列として持つこと。

## 進捗

- [ ] Phase 1 操作的容量領域 (主語) 📋
- [ ] Phase 2 補助変数 union (独立・後回し可) 📋
- [ ] Phase 3 協調外界 (安い外界) 📋
- [ ] Phase 4 UV outer bound (本命) 📋
- [ ] Phase 5 一致クラスの拡張 📋

## 在庫 (2026-07-26 時点、すべて sorry 0)

| 資産 | 場所 | 用途 |
|---|---|---|
| `marton_achievability` | `BroadcastChannel/Marton/Achievability.lean:767` | 一般 BC の内界 (EGK Thm 8.3、private message のみ)。Phase 1 の入力 |
| `InMartonRegion` | `Marton/Basic.lean:40` | 3 不等式バンドル (点ごと述語)。集合版の素材 |
| `bc_converse` / `bc_achievability` | `BroadcastChannel/Converse.lean:598` / `Achievability/Assembly.lean:1093` | degraded 限定の内外一致。Phase 5 の既存到達点 |
| `csiszar_sum_identity` | `BroadcastChannel/ConverseGateway.lean:118` | **任意の 2 系列に対する一般形**で証明済。Phase 4 の核 |
| `bc_input_singleletterize` | `Converse.lean:343` | degraded 単一文字化。Phase 4 は degradedness 前提を抜いた再構成 |
| `MACAchievable` / `macCapacityRegion` / `macPentagon` | `MultipleAccess/TimeSharing.lean:49,66,58` | **Phase 1 の雛形**。操作的述語 → closure で集合化のパターン |
| `mac_capacity_region_reconciliation` | `MultipleAccess/Reconciliation.lean:292` | 内外を同じ言語に揃える先例 |
| `MeasureFano` / `channel_coding_converse_general_memoryless_pure` | Fano / ChannelCoding 配下 | Phase 3・4 の converse 基盤 |

**存在しないもの**: 一般 BC の外界 (0 本)。BC の操作的到達可能性述語 (`BCAchievable` 相当が無い。
MAC と WynerZiv にはある)。集合としての BC 容量領域。less noisy / more capable / semi-deterministic
の定義 (project 全体で 0 hit)。

## ゴール / Approach

**「まず外界」は半分正しい。その前に主語が要る。**

現状、一般 BC の容量領域は Lean のオブジェクトとして**存在しない**。degraded 用の
`InBCCapacityRegion` は「与えられた 2 つの情報量に対して rate pair が入るか」という点ごとの
不等式バンドルで、集合ではない。未解決問題は「この集合は何か」という問いなので、集合としての
主語が無いと問いそのものが書けず、外界を建てても内界と突き合わせる言語が無い。

そこで **Approach は「主語 → 安い外界で挟み込みの骨格 → 本命の外界 → 一致クラスの拡張」** の 4 段。
外界の重い仕事 (Phase 4) の前に、Phase 1 で `bcCapacityRegion W : Set (ℝ × ℝ)` を定義し、Phase 3 の
緩い外界で **一度挟み込みを完成させてしまう**。以後の外界の改良はすべて「同じ挟み込みの右辺を
狭める」差分作業になり、1 本ごとに独立して価値が出る。逆順 (先に UV outer bound を作る) だと、
最も重い Phase が最初に来るうえ、完成しても内界と並べられない。

MAC 側に `MACAchievable` → `macCapacityRegion := closure {...}` という完成した先例があるので、
Phase 1 は設計判断がほぼ不要な写経で済む。ここが「外界より先」を安く正当化している。

## Phase 詳細

### Phase 1 — 主語を作る (操作的容量領域) ★最優先・低リスク

- [ ] `BCAchievable (W) (R₁ R₂) : Prop` — 両受信者の平均誤り確率が任意の `ε'` 未満。
      `MACAchievable` (TimeSharing.lean:49) と同型、`averageErrorProb₁ / ₂` の 2 本立てにするだけ
- [ ] `bcCapacityRegion (W) : Set (ℝ × ℝ) := closure {p | BCAchievable W p.1 p.2}`
      (closure を取る理由も MAC と同じ: 厳密不等号で述べた達成可能集合は閉じていない)
- [ ] `bc_achievable_mono` — down-set 性 (`mac_achievable_mono` を写す)
- [ ] `martonRegion pV K W : Set (ℝ × ℝ)` — `InMartonRegion` の集合版 (単一補助変数分布)
- [ ] **`marton_region_subset_capacity`** : `martonRegion pV K W ⊆ bcCapacityRegion W`
      — `marton_achievability` の厳密不等号形を `∀ε'` 抽象に持ち上げ、境界は closure で回収

**成果**: 内界が集合の言葉になる。以後どの外界が来ても即座に挟み込みが書ける。

### Phase 2 — 補助変数についての union (独立、後回し可)

Phase 1 の `martonRegion` は `(pV, K)` を引数に取る。真の Marton 内界は補助変数の型と分布に
ついての和集合。

- [ ] 型量化の回避: `V₁ V₂ : Type*` の量化は universe 問題を生むので、濃度を `Fin k` に固定して
      `k` について union する形を採る
- [ ] Carathéodory 型の濃度上界 (補助変数のアルファベットを入力アルファベットで抑える) は
      Mathlib にも in-repo にも無い。**自作コストが読めないので、濃度固定版で止めるのが honest**
- [ ] time-sharing / convex hull が要るなら `MultipleAccess/TimeSharingConverse/` の資産を参照

**Phase 3–4 の前提ではない**。挟み込みだけなら Phase 1 の点ごとの形で言える。コスト不明のため
park 可能。ここで詰まっても本線は止まらない配置にしてある。

### Phase 3 — 協調外界 (安い外界) ★短期で挟み込みが完成する

2 人の受信者が出力を持ち寄れるとした単一ユーザー通信路に帰着させる。

- [ ] 個別 rate の外界 (各受信者を単独の単一ユーザー通信路と見る) — 既存の単一ユーザー converse
      をほぼそのまま適用
- [ ] 和 rate の外界 (協調受信) — 同上、出力対を 1 つの出力と見る
- [ ] `bcOuterRegionCoop W : Set (ℝ × ℝ)` + `bc_capacity_subset_coop`

**成果**: 「外界 0 本」を脱し、`martonRegion ⊆ bcCapacityRegion ⊆ bcOuterRegionCoop` が揃う。
緩い外界だが、**構造としては未解決問題の全景がこの時点で Lean に載る**。

### Phase 4 — UV outer bound (Nair–El Gamal) ★本命・最重量

- [ ] degraded 版 `bc_input_singleletterize` の単一文字化を、degradedness 前提 `h_deg_block` 抜きで
      再構成する。degraded 版は entropy-difference route で `h_deg_block` を使って右辺の雑音項を
      潰していたので、それが落ちる分だけ補助変数が残る形になる
- [ ] 核となる Csiszár 和恒等式は**既に一般形で証明済** (`csiszar_sum_identity`、任意の 2 系列)。
      Phase 4 の主コストは恒等式そのものではなく補助変数の identification 側にある
- [ ] 構造前提の扱いは degraded 版と同じ方針を踏襲: memoryless / d-separation の帰結は
      graphoid machinery が Mathlib に無いため**明示的な構造前提として受け取る** (load-bearing では
      なく channel の性質を符号化したもの、という既に確立した honest なパターン)
- [ ] `bcOuterRegionUV W : Set (ℝ × ℝ)` + `bc_capacity_subset_uv`

**難所**: 補助変数の identification。degraded 版は 1 本 (`Uᵢ = (W₂, Y₂^{<i})`) で済んだが、UV 外界は
3 本を同時に扱う。ここが閉じるかで Phase 4 の成否が決まる。

### Phase 5 — 一致するクラスを広げる ★新しい定理が実際に閉じる場所

degraded は既に閉じている。その一般化を、Phase 1 の内界と Phase 4 の外界の組で回収する。

- [ ] クラス定義の新設 (project に 0 hit): more capable / less noisy / semi-deterministic
- [ ] **semi-deterministic BC** (Marton 1979) — Marton 内界 = 容量領域が既知。Phase 1 と Phase 4 が
      揃えば等号が閉じる。**本計画で最も費用対効果が高い到達点**
- [ ] more capable / less noisy — 外界が UV より単純な形を取る (El Gamal 1979)
- [ ] degraded を新クラスの特殊化として既存 `bc_converse` / `bc_achievability` に接続

## 未解決本体との距離 (正直な見積り)

「Marton 内界 = 一般 BC の容量領域か」は **open**。数学が存在しないので形式化できない。本計画が
終わっても未解決問題は未解決のままで、得られるのは以下。

- 内界・外界・容量領域が同一言語で並び、**ギャップが機械可読な形で固定される**
- 特定の BC で内外が分離するかを検証する基盤 (反例候補の検算)
- 一致が既知の特殊クラスについては、等号が実際に閉じる (Phase 5)

期待値は「厳密な足場 + 教材価値」に置くのが妥当。形式化が情報理論の未解決問題の解決に直接
寄与した前例は無い、という前提で計画している。

## 設計上の未決事項 (先に決めると後戻りが減る)

1. **領域を `Set (ℝ × ℝ)` にするか点ごと述語で通すか** → 挟み込みを言うなら集合。MAC に先例あり。
   ただし既存の `InMartonRegion` / `InBCCapacityRegion` は残し、集合版から参照する二層構成にする
   (既存 headline の署名を触らずに済む)
2. **補助変数 union の射程** (Phase 2) — 濃度固定で止めるか Carathéodory を自作するか
3. **外界の第一目標** — Phase 4 を UV にするか、より単純な Körner–Marton (common message 付き) や
   Sato 外界 (同一 marginal を持つ BC 全体についての交差 + MAC converse 再利用) から入るか

## 撤退ライン (frozen slug)

| slug | 発動条件 | 退避先 |
|---|---|---|
| **L-BCO1** | Phase 4 の補助変数 identification が閉じない | Körner–Marton 外界 (構造が単純) または Sato 外界 (既存 MAC converse を再利用) へ後退 |
| **L-BCO2** | Phase 2 の型量化 union が universe 問題で詰む | 濃度固定版で止め、union は取らない (Phase 3–5 は影響を受けない) |
| **L-BCO3** | Phase 5 の等号が Phase 4 の外界の形と噛み合わない | クラス定義だけ入れて等号は defer |

**禁止事項**: どの撤退でも「外界が成立する」「補助変数が取れる」等を `*Hypothesis` 述語に束ねて
仮説として渡す形は取らない (CLAUDE.md 検証の誠実性 tier 5)。退避は `sorry` + `@residual` で、
署名は証明したい形のまま保つ。

## 推奨実行順

**Phase 1 → 3 → 4 → 5**。Phase 2 は独立で、いつ入れてもよいし入れなくても本線は完結する。
Phase 1 と 3 は既存資産の写経に近く、合わせて 1〜2 leg で挟み込みの骨格まで到達する見込み。
Phase 4 が本計画の重心。

## 判断ログ

- **外界より先に操作的容量領域を定義する** (本計画の起点): 一般 BC の容量領域が Lean のオブジェクト
  として存在せず、外界を建てても内界と突き合わせる言語が無いため。MAC 側に完成した雛形があり
  安い。この順序を崩すと最重量の Phase 4 が最初に来て、しかも単独では挟み込みにならない。
