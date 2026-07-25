# Shannon: 一般 BC の Marton inner bound サブ計画

> **Parent**: [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md) §L-BC5 (解除)

**Status**: 🚧 進行中 — degraded 仮定を外した一般 (non-degraded) two-receiver broadcast channel に対する
**Marton inner bound (El Gamal–Kim *Network Information Theory* Thm 8.3、private message のみ)** の形式化。
親 plan の撤退ライン **L-BC5** (一般 BC + Marton は完全 scope-out) を**ユーザー指示で解除**して追う。
Phase 1/2/3/4 完了 (second moment 中核 + 鋭化 + region 述語 + 5-tuple ambient、root 登録済)、Phase 5-8 未着手。
**SoT**: 在庫 [`marton-inner-bound-inventory.md`](marton-inner-bound-inventory.md) + 本 plan。詳細履歴は git。
**再検証** (prose にキャッシュしない):
`scripts/sig_view.ts --sorry InformationTheory/Shannon/BroadcastChannel/Marton/*.lean` /
`#print axioms InformationTheory.Shannon.BroadcastChannel.Marton.meas_pairCount_eq_zero_le` /
`rg -n "Marton" InformationTheory.lean` (root 登録の有無)。

## 進捗

- [x] Phase 0 — Mathlib / in-project 在庫調査 ✅ → [`marton-inner-bound-inventory.md`](marton-inner-bound-inventory.md)
- [x] Phase 1 — mutual covering の second moment 中核 (抽象 `S` 版) ✅ `Marton/MutualCovering.lean` (cd5c379a)
- [x] Phase 2 — region 述語 + レート分割の消去補題 + root 登録 ✅ `Marton/Basic.lean` (fa43fcb6)
- [x] Phase 3 — 5-tuple ambient plumbing + `martonInfo₁/₂/V₁V₂` ✅ `Marton/Setup.lean` (5800094e)
- [x] Phase 4 — 共分散の鋭化 (conditional slice 版) ✅ `MutualCovering.lean` 追記 (6183832d) ★ sum-rate 制約の要
- [ ] Phase 5 — typicality 具体化 = `marton_mutual_covering` 📋
- [ ] Phase 6a — 受信機 1 の誤り解析 (選択索引の独立性) 📋
- [ ] Phase 6b — 受信機 2 の誤り解析 + averaged swap 📋
- [ ] Phase 7 — 組み立て = headline `marton_achievability` 📋
- [ ] Phase 8 — 2 ゲート + README + 親 plan 同期 + proof-log 📋

---

## ゴール / Approach

**到達目標**: 一般 BC `W : BCChannel α β₁ β₂` と補助変数の同時分布 `pV : Measure (V₁ × V₂)`、
入力カーネル `K : Kernel (V₁ × V₂) α` に対し、3 本の制約

```
R₁ < I(V₁;Y₁)                      -- martonInfo₁
R₂ < I(V₂;Y₂)                      -- martonInfo₂
R₁ + R₂ < I(V₁;Y₁) + I(V₂;Y₂) − I(V₁;V₂)   -- martonInfoV₁V₂ を差し引いた sum-rate
```

を満たす `(R₁,R₂)` が達成可能 (十分大きい `n` で平均誤り確率が両受信機とも `ε'` 未満の
`BroadcastCode M₁ M₂ n α β₁ β₂` が存在する) こと。

**全体戦略は 3 層に分ける**。層の境界は「抽象度」で切ってあり、下層は上層の定義を一切知らない。

1. **抽象 second-moment 層** (Phase 1、完了): 可測集合 `S ⊆ α × β` と
   `iIndepFun (codebookFamily X Y) μ` だけを仮定して
   `P(どの組も S に落ちない) ≤ (M₁+M₂)/(M₁M₂p)` を出す層。typicality を一切参照しない。
2. **typicality 層** (Phase 3–5): `S := jointlyTypicalSet μ V₁s V₂s n ε` と具体化し、
   `p` の下界 (既存 `jointlyTypicalSet_indep_prob_ge`) と conditional slice の一様上界 `q̄`
   (既存 `conditionalTypicalSlice_card_le` × `typicalSet_prob_le`) を指数形で供給する層。
3. **operational 層** (Phase 6–7): 符号帳から `BroadcastCode` を作り、Bonferroni + averaged swap +
   pigeonhole で平均誤り確率を落とす層。既存 `bc_achievability` の骨格を写経する。

**符号帳の索引設計 (本 plan で確定させる中核の設計判断)**: Marton の符号帳は
**メッセージ索引と covering 索引の直積** `Fin Mᵢ × Fin M̃ᵢ` を持つ。
`M̃ᵢ = ⌈exp(n R̃ᵢ)⌉` は「1 メッセージあたりの副符号帳サイズ」。符号化器は与えられた `(m₁,m₂)` に対し
副符号帳の組 `(l₁,l₂)` を joint typical になるよう選ぶ (= mutual covering の適用点、固定 `(m₁,m₂)` ごとに
2 本の副符号帳は独立なので Phase 1 の定理がそのまま当たる)。復号器は `(mᵢ,lᵢ)` の組を復号する。
これで制約は

```
covering : R̃₁ + R̃₂ > I(V₁;V₂)
decode 1 : R₁ + R̃₁ < I(V₁;Y₁)
decode 2 : R₂ + R̃₂ < I(V₂;Y₂)
```

の 3 本になり、`(R̃₁,R̃₂)` を消去すると目標の 3 本が出る (Phase 2 の Fourier–Motzkin 補題)。
**逆向きも初等**: `R̃ᵢ := (Iᵢ − Rᵢ)·θ`、`θ ∈ (I₁₂/D, 1)`、`D := (I₁−R₁)+(I₂−R₂)` と取れば
3 本すべてが満たされる (`D > I₁₂` が sum-rate 制約そのもの)。

**入力側の randomization は符号帳アンサンブルに置く**。`K` はカーネルだが `BroadcastCode.encoder` は
決定的写像なので、`bc_achievability` の satellite 段と同じく `X^n` を符号帳の 1 段として
`Πᵢ K(v₁ᵢ, v₂ᵢ)` から引き、pigeonhole で実現値を固定する。構造体の改修は不要。

**既存資産の再利用率**: 誤り解析 + 組み立て (Phase 6–7) は
`BroadcastChannel/Achievability/{ErrorAnalysis,Assembly}.lean` の写経が主で、
net-new は (a) mutual covering の typicality 具体化、(b) 選択索引 `(L₁,L₂)` が符号帳全体の関数である
ことに由来する独立性の扱い、の 2 点に局在する。

---

## 確定済みの設計判断 (実装 leg の前提)

### D1. 決定的関数 `x = f(v₁,v₂)` は採らず、一般カーネル `K : Kernel (V₁ × V₂) α` 形で述べる

在庫 §4.2 の最重要所見。`Kernel.deterministic f` を入れると `(K v).real {b} = 0` (`b ≠ f v`) となり、
in-project の typicality mass bound が**例外なく要求する full support 前提**
(`hK : ∀ v a, 0 < (K v).real {a}`) と原理的に両立しない。強 typicality 版も同じ前提を要求するため
ルート変更では回避できない。教科書側も一般カーネルを許して領域が拡大しないことが知られており、
数学的損失はない。既存 `bc_achievability` も同じ full support 前提を持つのでプロジェクト内で一貫する。

⇒ **この射程の差 (EGK Thm 8.3 の逐語形である決定的関数版ではない) は headline docstring に明示する**
(Phase 7 の受け入れ条件)。「一般カーネル形で述べており、決定的 `x = f(v₁,v₂)` 版は本定理の直接の系
としては出ない」ことを 1–2 文で書く。

### D2. 構造改修はしない (逆依存を機械実測して確認)

`scripts/dep_consumers.sh` の実測値:

| 対象 | direct consumers | 扱い |
|---|---|---|
| `InformationTheory.Shannon.BroadcastChannel.BroadcastCode` | **19 decl / 5 file** (Basic 10 / Converse 5 / ErrorAnalysis 2 / Setup 1 / Assembly 1) | 符号化器の型がそのまま使えるので**無改修**。blast radius 0 |
| `InformationTheory.Shannon.BroadcastChannel.InBCCapacityRegion` | **3 decl / 2 file** (`Basic.lean:139 .mono` / `Converse.lean:179 bc_converse_message_level` / `Converse.lean:583 bc_converse`) | 制約が 2 本しかないので 3 本目が要るが、**既存を改修せず `InMartonRegion` を新規追加**する |

### D3. headline の rate 制約は**厳密不等号**で置く (`InMartonRegion` を仮説に取らない)

既存 `bc_achievability` (`Achievability/Assembly.lean:1087`) の署名を逐語確認した結果、あれは
`InBCCapacityRegion` を仮説に取らず `hR₁lt : R₁ < bcInfo₁ pU K W` / `hR₂lt : R₂ < bcInfo₂ pU K W` の
**厳密不等号 2 本**を直接取っている (`InBCCapacityRegion` は converse 側専用)。
在庫 §1.1 の想定署名は `hmarton : InMartonRegion …` (非厳密 `≤`) だったが、**achievability に境界は
乗らない**ので厳密形が正しい。⇒ headline は厳密不等号 3 本、`InMartonRegion` (`≤` 3 本) は
region 記述 / README / 将来の converse 用として別途定義する。

### D4. Phase 1 の分散上界は**粗い版**であり、そのままでは sum-rate 制約に届かない ★

Phase 1 の `variance_pairCount_le` は添字を共有する組に対し `cov ≤ pairProb` (= `p`) という
一様上界を使っている (`MutualCovering.lean:198` `covariance_pairIndicator_le` を逐語確認)。
結果として得られる `meas_pairCount_eq_zero_le` の結論は

```
P(A = 0) ≤ (M₁ + M₂)/(M₁ M₂ p) = 1/(M₂ p) + 1/(M₁ p)
```

で、これが 0 に落ちるには **`M₁ p → ∞` かつ `M₂ p → ∞`** が要る。`p ≈ exp(−n·I(V₁;V₂))` なので
条件は `R̃₁ > I(V₁;V₂)` **かつ** `R̃₂ > I(V₁;V₂)` — 教科書の **`R̃₁ + R̃₂ > I(V₁;V₂)` (和)** より真に強い。
消去すると `R₁ + R₂ < I₁ + I₂ − 2·I(V₁;V₂)` という**弱い領域**しか出ない。

鋭い版に必要なのは、添字を 1 本だけ共有する組に対する共分散の評価である。共有項の寄与が
`q̄/(M₁p) + q̄/(M₂p)` となり、typicality 具体化では `q̄/p ≤ exp(6nε)/(1−η)` で抑えられるので
**`M̃ᵢ → ∞` だけで消える**。残るのは対角項 `1/(M₁M₂p)` = **和条件**そのもの。

**スライス上界は両方向が要る (実装時に反例で確定)**。fst 共有側は `∫ q(x)² dμX ≤ q̄·p`
(`q x := μY(x での β-fiber)`) に落ちるが、snd 共有側は `∫ r(y)² dμY` (`r y := μX(y での α-fiber)`)
に落ちる。**μY 側の一様上界は μX 側を全く抑えない**ので、片方向だけを仮定した主張は偽:

> `α = {0}`, `β = {0,1}`, `μX = δ₀`, `μY(0) = ε`, `μY(1) = 1−ε`, `S = {(0,0)}`。
> β-fiber 上界は `ε`、`p = ε`。snd 共有組の共分散は `Var(1[Y=0]) = ε−ε²` で、
> 主張される上界 `q̄·p = ε²` を `ε = 0.1` で破る (`0.09 > 0.01`)。

⇒ `covariance_pairIndicator_shared_le` は `hsliceY` (x を固定した β-fiber) と
`hsliceX` (y を固定した α-fiber) の**両方**を取る。どちらも `S` と `μX`, `μY` の構造的な量的性質であり、
結論を担ぐ仮説ではない (核は second moment + Chebyshev のまま)。

⇒ **Phase 4 を独立の Phase として立てる** (在庫にはこの区別がない)。ここが閉じないときの退避は
L-MT5 (弱化領域を headline にし、鋭化を別 plan へ split) — **不発動**。

---

## Phase 詳細

各 Phase に「入力 / 出力 / 見積り行数 / 先行 Phase / proof-log」を書く。行数は在庫 §7 の見積りから
Phase 1 の実績 (397 行) を差し引いて再配分したもの。

### Phase 0 — 在庫調査 ✅ 完了

出力 = [`marton-inner-bound-inventory.md`](marton-inner-bound-inventory.md)。
Mathlib 壁 0 件 / 既存率 89% / 自前構築 8 種。**proof-log: no**。

### Phase 1 — mutual covering の second moment 中核 (抽象 `S` 版) ✅ 完了

- 入力: なし (Mathlib の `variance_sum` / `covariance_eq_sub` / `IndepFun.covariance_eq_zero` /
  `meas_ge_le_variance_div_sq` のみ)。
- 出力: `InformationTheory/Shannon/BroadcastChannel/Marton/MutualCovering.lean` (commit `cd5c379a`)。
  中核 4 段 = `integral_pairCount` (第 1 モーメント) / `covariance_pairIndicator_eq_zero`
  (添字を共有しない組の共分散 0) / `variance_pairCount_le` (分散上界) /
  `meas_pairCount_eq_zero_le` (Chebyshev)。正準 i.i.d. ambient 上での充足可能性証明書
  `meas_pairCount_ambient_eq_zero_le` 付き (仮説が供給不能で空回りするリスクは潰れている)。
- 設計: 独立性は `iIndepFun (codebookFamily X Y) μ` の **1 本**で与える。`codebookFamily` は
  2 本の符号帳を `Fin M₁ ⊕ Fin M₂` 添字の単一族へ interleave し、未使用座標を定数 padding して
  終域を `α × β` に揃えたもの。代償は `[Nonempty α] [Nonempty β]` のみ。
- **未実施**: `InformationTheory.lean` への import 登録 (意図的、Phase 2 で行う)。
- **proof-log: no** (Phase 5 の proof-log に統合する)。

### Phase 2 — region 述語 + レート分割の消去補題 + root 登録 📋

- 入力: なし (純粋な実数の不等式)。
- 出力: `InformationTheory/Shannon/BroadcastChannel/Marton/Basic.lean`
  - `structure InMartonRegion (R₁ R₂ I₁ I₂ I₁₂ : ℝ) : Prop` — `bound₁` / `bound₂` / `boundSum` の 3 フィールド
    (`InBCCapacityRegion` は改修しない → D2)。
  - `InMartonRegion.mono` — `I₁ ≤ I₁'`, `I₂ ≤ I₂'`, **`I₁₂' ≤ I₁₂`** (第 3 引数だけ向きが逆) で単調。
  - `exists_martonRateSplit` — Fourier–Motzkin。厳密 3 本 `R₁ < I₁`, `R₂ < I₂`,
    `R₁+R₂ < I₁+I₂−I₁₂` から
    `∃ R₁' R₂', 0 ≤ R₁' ∧ 0 ≤ R₂' ∧ I₁₂ < R₁'+R₂' ∧ R₁+R₁' < I₁ ∧ R₂+R₂' < I₂` を作る。
    構成は `Rᵢ' := (Iᵢ−Rᵢ)·θ`、**`θ := max ((I₁₂/D + 1)/2) (1/2)`**、`D := (I₁−R₁)+(I₂−R₂)`。
    `I₁₂ ≥ 0` が不要なのは正しいが、**クランプなしの素の `θ` は `I₁₂ < −D` で負になり `0 ≤ Rᵢ'` を破る**
    (機械確認済)。`R̃` の合成チルダ (U+0303) は Lean の識別子として不正なのでプライム記法を使う。
  - `InformationTheory.lean` に `Marton.MutualCovering` と `Marton.Basic` の import を追加
    (BC ブロックは現状 `InformationTheory.lean:95-101`、その直後に足す)。
    まだ誰にも消費されていない段階で登録するのは、`scripts/dep_*.sh` と CI に見えるようにするため。
- 見積り: **90–130 行**。先行: なし。**proof-log: no**。

### Phase 3 — 5-tuple ambient plumbing + 情報量 📋

- 入力: `BroadcastChannel/Achievability/Setup.lean:54,71,159,172,182,212,247` (4-tuple 版の写経元)。
- 出力: `InformationTheory/Shannon/BroadcastChannel/Marton/Setup.lean`
  - `martonJointDistribution pV K W : Measure (V₁ × V₂ × α × β₁ × β₂)` — `pV ⊗ₘ K ⊗ₘ W` を
    `MeasurableEquiv.prodAssoc` で整形 (`bcJointDistribution` より入れ子が 1 段深い)。
  - `martonAmbientMeasure` (`Measure.infinitePi`) + 座標補題 4 本 (`map_coord` / `iIndepFun_coord` /
    `identDistrib_coord` / `coord_marginal_pos`) + `singleton_pos` 相当。
  - `martonInfo₁ = I(V₁;Y₁)` / `martonInfo₂ = I(V₂;Y₂)` / `martonInfoV₁V₂ = I(V₁;V₂)` を
    **entropy 差分形**で定義 (`bcInfo₁` `Setup.lean:111` と同形)。`mutualInfo` (`ℝ≥0∞`) は使わない
    — typicality の出口形と噛み合わないため。
- 落とし穴: `entropy` は `[Fintype] [DecidableEq] [Nonempty] [MeasurableSpace] [MeasurableSingletonClass]`
  を要求 (`Bridge.lean:34`)。5-tuple の各射影に instance を通す必要がある。
- 見積り: **360–550 行**。先行: Phase 2。**proof-log: no** (定型写経)。

### Phase 4 — 共分散の鋭化 (conditional slice 版) ✅ 完了 ★

- 出力: `Marton/MutualCovering.lean` への追記 (397 → 718 行、11 decl 追加、commit `6183832d`)。
  - `covariance_pairIndicator_shared_le` (L491) — 添字を 1 本だけ共有する組に対し `cov ≤ q̄ * pairProb`。
    仮説は `hsliceY` / `hsliceX` の**両方向** (→ D4 の反例)。
  - `variance_pairCount_le'` (L519) / `meas_pairCount_eq_zero_le'` (L585) — D4 の目標形どおり。
    第 1 項 `1/(M₁M₂p)` が和条件、残り 2 項が `q̄/p` 経由の個別条件、という分離が出ている。
- 既存の粗い版 4 本は**署名も結論も無改変** (`q̄` を供給できない文脈の fallback として残す)。
  `variance_pairCount_le` の証明内部のみ、局所 `have` 2 本を `private lemma` へ切り出して鋭い版と共有。
- 設計 (再利用価値あり): Tonelli を Bochner でなく **lintegral (`ℝ≥0∞`) で回す**と可積分性の議論が消え、
  3 本目の補題群が各 20 行で閉じる。積型は **`α × (β × β)`** の向き (共有座標を最外) が決定的で、
  `(α × β) × β` だと Tonelli が噛まない。
- 撤退 L-MT5 は**不発動**。**proof-log: yes** (Phase 5 の proof-log に統合)。

### Phase 5 — typicality 具体化 = `marton_mutual_covering` 📋

- 入力: Phase 3 (ambient / 情報量 / **`martonAmbient_entropy_coord`** = ambient 上の entropy を
  per-coordinate 版へ落とす補題。情報量を典型集合の指数と噛ませる際に必ず要る)、Phase 4 (鋭い評価)、既存
  `jointlyTypicalSet_indep_prob_ge` (`RateDistortion/AchievabilityJointTypicalEncoder.lean:255`) /
  `conditionalTypicalSlice_card_le` (`SlepianWolf/ConditionalTypicalSlice.lean:140`) /
  `typicalSet_prob_le` (`AEP/Basic/Achievability.lean:507`) /
  `jointlyTypicalSet_prob_tendsto_one` (`ChannelCoding/Basic.lean:450`)。
- **新規に要る橋 1 本** (Phase 4 実装時に実測、在庫にも本 plan 初版にも無かった項目):
  Phase 4 の仮説は両方向 (`hsliceY` / `hsliceX`) を要求するが、in-project 資産は**片方向しか無い**。
  `conditionalTypicalSlice_card_le` (`SlepianWolf/ConditionalTypicalSlice.lean:140`) は
  定義 (`:51`) が `{ x | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε }` = **X-fiber** なので `hsliceX` 側は直接供給できる。
  `hsliceY` (Y-fiber) 側の補題は `rg` で 0 件。`jointlyTypicalSet` の定義 (`ChannelCoding/Basic.lean:281`)
  自体は X/Y について対称なので、`jointlyTypicalSet μ Ys Xs n ε = Prod.swap ⁻¹' jointlyTypicalSet μ Xs Ys n ε`
  相当の輸送補題 (entropy 不変性経由) か `conditionalTypicalSlice_card_le` の鏡像を建てる。**壁ではなく配線、40–80 行**。
- 出力: `Marton/Covering.lean`
  - `S := jointlyTypicalSet μ V₁s V₂s n ε` への具体化 (`α := Fin n → V₁`, `β := Fin n → V₂`)。
  - 符号帳 ambient の配線: `Ω := Codebook M̃₁ n V₁ × Codebook M̃₂ n V₂`、
    `μ := (codebookMeasure pV₁ M̃₁ n).prod (codebookMeasure pV₂ M̃₂ n)`、
    `X i c := c.1 i` / `Y j c := c.2 j` に対し `iIndepFun (codebookFamily X Y) μ` を供給する。
    ルート: `MeasurableEquiv.sumPiEquivProdPi` + `measurePreserving_sumPiEquivProdPi`
    (`Mathlib/MeasureTheory/Constructions/Pi.lean:774/790`) で和型添字の `Measure.pi` へ移し、
    `iIndepFun_pi` → `.comp ambientPad` (Phase 1 の `iIndepFun_codebookFamily_ambient` の証明を写経)。
  - 指数評価: `p ≥ (1−η)·exp(−n(I₁₂+3ε))` / `q̄ ≤ exp(−n(I₁₂−3ε))` を合成し
    `q̄/p ≤ exp(6nε)/(1−η)`。`η` は自由パラメータなので `η ≤ 1/2` 等で固定する
    (在庫 §6 の注意点)。`v₁` が非 typical な場合はスライスが空
    (`conditionalTypicalSlice_empty_of_y_not_typical`) — 場合分けを落とすと `typicalSet_prob_le` の
    `hx` が立たない。
  - headline: `marton_mutual_covering` — `R̃₁ + R̃₂ > I₁₂` かつ `R̃ᵢ > 0` のとき
    `∃ N, ∀ n ≥ N, (符号帳測度).real {joint typical な組が 1 つも無い} < η'`。
- 見積り: **300–480 行** (swap 橋 40–80 行を含む)。先行: Phase 3, 4。**proof-log: yes**。
- 撤退: L-MT1。

### Phase 6a — 受信機 1 の誤り解析 📋

- 入力: `bc_errorProbAt₁_le_bonferroni3` (`ErrorAnalysis.lean:652`) /
  `macJTS_indep_prob_le_X1` (`MultipleAccess/AchievabilityCore.lean:50`) / Phase 5。
- 出力: `Marton/ErrorAnalysis.lean` の受信機 1 側。誤り事象を
  (E0) 選ばれた `(l₁,l₂)` の組が joint typical でない — Phase 5 が潰す /
  (E1) 真の `(m₁,l₁)` と `y₁` が joint typical でない — typicality LLN /
  (E2) 偽の `(m₁',l₁')` と `y₁` が joint typical — `R₁+R̃₁ < I(V₁;Y₁)` が潰す、に分解。
- **本 Phase 最大の解析リスク**: 選択索引 `(L₁,L₂)` が符号帳**全体**の関数なので、
  「偽の符号語 `V₁^n(m₁',l₁')` が `Y₁^n` と独立」という素朴な主張は選択の条件付けを通ると崩れる。
  緩和策は既存の averaged swap (`bc_random_codebook_E0₁_swap` `Assembly.lean:97`) と同じく、
  符号帳測度上の平均を先に取ってから交換すること。ここは gateway-atom-first の対象
  — 本 Phase に入る前に E2 の 1 原子だけを先に撃って通ることを確認する。
- 見積り: **450–650 行**。先行: Phase 5。**proof-log: yes**。
- 撤退: L-MT4 / L-MT6。

### Phase 6b — 受信機 2 の誤り解析 + averaged swap 📋

- 入力: Phase 6a の受信機 1 側 (対称なので写経)、`bc_errorProbAt₂_le_bonferroni` (`ErrorAnalysis.lean:28`)。
- 出力: `Marton/ErrorAnalysis.lean` の受信機 2 側 + 平均誤り確率への変換
  (`bc_averageErrorProb₁_toReal_le` / `bc_averageErrorProb₂_toReal_le` の相当物)。
- BC (degraded) と違い **cloud/satellite の 2 段構造がない**ので、受信機 2 は受信機 1 の完全な鏡像。
  逆に degraded 版にあった `bcInfoJoint` / wrong-cloud の段は**まるごと不要**。
- 見積り: **350–450 行**。先行: Phase 6a。**proof-log: no** (6a の写経)。

### Phase 7 — 組み立て = headline `marton_achievability` 📋

- 入力: Phase 2 (`exists_martonRateSplit`)、Phase 5、Phase 6a/6b、
  `bc_two_tier_pigeonhole` (`Assembly.lean:699`、完全に抽象なのでそのまま呼べる)、
  `bcCodebookToCode` (`Setup.lean:678`) の相当物。
- 出力: `Marton/Achievability.lean`
  - `martonCodebookToCode` — 3 段符号帳 + 選択関数から `BroadcastCode M₁ M₂ n α β₁ β₂` を作る。
    選択は `Classical.choice` 経由の非構成的な選択になる (既存 `bcCodebookToCode` と型が違う点に注意)。
  - headline `marton_achievability` — 署名は在庫 §1.1 を D3 に従って厳密不等号 3 本へ差し替えた形。
  - **docstring 要件** (D1): 一般カーネル形であること + 決定的 `x = f(v₁,v₂)` 版は直接の系として
    出ないこと + `hpV`/`hK`/`hW` が full support の**正則性前提**であること (load-bearing ではない) を明記。
- ε の配分は 5 系統 (covering 失敗 / E0₁ / E0₂ / alias₁ / alias₂)。
- 見積り: **250–400 行**。先行: Phase 2, 5, 6a, 6b。**proof-log: yes**。
- 撤退: L-MT6。

### Phase 8 — 2 ゲート + README + 親 plan 同期 + proof-log 📋

- `honesty-auditor` (新規 `sorry` + `@residual` を導入した Phase があれば必須) と
  `style-auditor` (`.lean` decl/docstring を触った全 Phase) を、触ったファイルに対して起動。
- `docs/readme-theorems.txt` に headline を追記 → `deno run -A scripts/gen_readme_table.ts --write`。
  Ch.15 行に degraded 版と並べる (章の対応は `docs/textbook-roadmap.md` Ch.15)。
- 親 plan 同期 (下記「親への同期指示」)。
- `deno run -A scripts/plan_lint.ts docs/shannon/marton-*.md docs/shannon/broadcast-channel-moonshot-plan.md`。
- **proof-log: no** (Phase 4/5/6a/7 の proof-log を統合する metrics のみ)。

---

## 撤退ライン (frozen slug — 他文書が参照しうる)

在庫 §9 の提案 L-MT1〜L-MT4 を採用し、番号は維持する (在庫が参照しているため)。
ただし **L-MT1 は射程を縮める**: 在庫が想定していた「4 ケース共分散分解」は Phase 1 で閉じたので、
L-MT1 が残って担うのは typicality 具体化 (Phase 5) のみ。鋭化 (Phase 4) と組み立て (Phase 7) は
新規スロット L-MT5 / L-MT6 に分ける。

| slug | 発動条件 | 退避 (= `sorry` + `@residual`。述語化して仮定に積むのは禁止) | 退避後に残るもの |
|---|---|---|---|
| **L-MT1** | Phase 5 の typicality 具体化 (符号帳 ambient 配線 or 指数合成) が 1 leg で閉じない | `marton_mutual_covering` の body を `sorry` + `@residual(plan:marton-inner-bound-plan)` にして、Phase 6–7 を先に組む | Phase 1–4 (抽象核 + 鋭化 + region + 情報量) は proof-done のまま。headline は条件付きにならず `sorry` 1 点に局在する |
| **L-MT2** | 決定的 `x = f(v₁,v₂)` 版が full support 前提と両立しない (D1、**既に発動・解決済**) | 一般カーネル `K : Kernel (V₁ × V₂) α` 形で主定理を述べる。決定的版は別 leg | 主定理はそのまま成立。失うのは EGK Thm 8.3 の逐語形との一致だけ (docstring に明示 → Phase 7 受け入れ条件) |
| **L-MT3** | Phase 3 の 5-tuple ambient plumbing が 4-tuple の写経で済まず爆発する | 補助変数を `V := V₁ × V₂` と束ねた 4-tuple `V × α × β₁ × β₂` に落とし、`bcAmbientMeasure` の形をそのまま保つ。射影 `V → V₁` / `V → V₂` を後付けする | 情報量の定義が射影経由になるだけで、Phase 4 以降の議論は不変 |
| **L-MT4** | Phase 6a の非構成的 encoder / 選択索引の独立性が既存 `bcCodebookToCode` 系と噛み合わない | sum-rate 制約なしの**退化版** (`R₁ < I(V₁;Y₁)`, `R₂ < I(V₂;Y₂)`、`V₁ ⟂ V₂`) を先に閉じる。mutual covering 不要 (`I₁₂ = 0`) で既存 MAC 型 union bound だけで通る | 一般 BC に対する (弱い) inner bound が headline として残る。degraded 仮定なしの結果なので単体で新規性がある |
| **L-MT5** | Phase 4 の鋭化 (3 変数独立性 + Tonelli) が閉じない | 粗い版 `meas_pairCount_eq_zero_le` のまま上を組み、headline の sum-rate 制約を `R₁+R₂ < I₁+I₂−2·I₁₂` に**弱化**する。真の Marton は `sorry` + `@residual(plan:marton-sharp-covering-plan)` で別 plan へ split | 弱化領域は Marton 領域に含まれる正しい inner bound なので、headline は無条件のまま (仮説束ねゼロ)。docstring に「教科書の領域より狭い」と明記する |
| **L-MT6** | Phase 7 の ε 配分 5 系統 / pigeonhole の合成が閉じない | headline を `sorry` + `@residual(plan:marton-assembly-plan)` に退避し、Phase 6 までの部品を proof-done として登録する | mutual covering / region / 情報量 / 誤り解析の部品はすべて無条件命題として残る |

> **禁止事項の再確認**: どの撤退ラインでも「covering が成立する」「選択索引が独立である」等を
> `*Hypothesis` 述語に束ねて仮説として渡す形は取らない (CLAUDE.md「検証の誠実性」tier 5)。
> 退避は必ず `sorry` + `@residual` で、署名は証明したい形のまま保つ。

---

## 親への同期指示 (親ファイルの編集は orchestrator が行う。本 plan では書き換えない)

`docs/shannon/broadcast-channel-moonshot-plan.md` に対し 3 箇所:

1. **Status 行 (`:3`)**: 先頭を `**Status**: CLOSED ✅` から
   `**Status**: degraded ✅ CLOSED / 一般 BC 🚧 進行中` へ。末尾の
   「一般 (non-degraded) BC + Marton (L-BC5) は scope-out 継続 (textbook-roadmap Ch.15)。」を
   「**L-BC5 (一般 BC + Marton) はユーザー指示で解除** → 子
   [`marton-inner-bound-plan.md`](marton-inner-bound-plan.md) で追跡 (Phase 1 = mutual covering の
   second moment 中核 完了)。Körner–Marton は scope-out 継続。」へ差し替える。
2. **要点の L-BC5 記述 (`:12`)**: **slug は凍結なので消さない**。
   「L-BC5 一般 (non-degraded) BC + Marton / Körner-Marton は完全 scope-out」を
   「L-BC5 一般 (non-degraded) BC + Marton / Körner-Marton は完全 scope-out **(Marton 部分は解除 →
   子 `marton-inner-bound-plan.md`。Körner–Marton は scope-out 継続)**」へ。
3. **Sub-plan 一覧テーブル (`:17-21`)** に 1 行追加 (plan_lint の双方向照合点):

   ```
   | [`marton-inner-bound-plan.md`](marton-inner-bound-plan.md) | L-BC5 解除 = 一般 BC の Marton inner bound (EGK Thm 8.3、private message のみ) | 🚧 進行中 (Phase 1 完了、Phase 2 以降 未着手) |
   ```

以降、本子 plan の進捗が動いたら 3 の状態欄を追随させる (衝突時は子が SoT)。

---

## Settled facts (再導出が高価なものだけ)

| claim | confidence | 再検証 | notes |
|---|---|---|---|
| Marton / mutual covering に対応する Mathlib 補題は存在しない (`"Paley"` / `"second_moment"` / `"covering_lemma"` はいずれも `Found 0 declarations`) | `loogle-neg` | 在庫 §8 のクエリを再実行 | 壁ではなく自前構築。近接テンプレ補題を各項目に名指し済 |
| 決定的カーネルは in-project typicality の full support 前提を原理的に壊す (`Kernel.deterministic` の質量が `b ≠ f v` で 0) | `machine` | `Mathlib/Probability/Kernel/Basic.lean:58` + `Mathlib/MeasureTheory/Measure/Dirac.lean:44` を Read | D1 の根拠。強 typicality 版も同じ前提を要求するのでルート変更で回避不能 |
| 粗い分散上界からは sum-rate 制約が出ない (D4) | `human-judgment` | Phase 4 の実装で機械確認する (`meas_pairCount_eq_zero_le'` が `1/(M₁M₂p)` 項を分離できるか) | 指数の算術による導出であり未機械検証。Phase 4 の受け入れ条件そのもの |

---

## 判断ログ

1. **先発 atom は second moment 中核 (在庫の推奨を採らなかった)**: 在庫 §9 は L-MT4 (退化版
   `V₁ ⟂ V₂`) を gateway atom に推していたが、退化版では mutual covering が自明化して**家系最大の
   難所を迂回してしまう**ため gateway として機能しない、と orchestrator が判断し second moment 中核を
   先発に据えた。結果 GO (Phase 1 完了)。L-MT4 は gateway ではなく Phase 6a の**退避先**として残す。
2. **D4 (粗い分散上界では sum-rate に届かない) は plan 起票時の新規所見**: 在庫は共分散の
   `q̄·p` 上界を #7-1 の内側に畳み込んでいて、粗い版と鋭い版の差が領域の大きさに直結することを
   分離していなかった。Phase 4 を独立 Phase として立て、L-MT5 を新設した。
3. **D3 (headline は厳密不等号) は在庫の想定署名の訂正**: 在庫 §1.1 は `hmarton : InMartonRegion …`
   (非厳密) を仮説に置いていたが、既存 `bc_achievability` の署名を逐語確認した結果、
   achievability 側は厳密不等号を直接取る形だった。`InMartonRegion` は region 記述用として定義する。
4. **層の境界を「抽象度」で切る**: Phase 1 が typicality を一切知らないことは偶然ではなく設計。
   Phase 4 の鋭化も抽象 `S` + 一様スライス上界 `q̄` の形で述べ、typicality 具体化は Phase 5 に閉じ込める。
   これにより Phase 4 が閉じなくても Phase 5 以降の骨格が変わらない (L-MT5 の退避が局所で済む)。
